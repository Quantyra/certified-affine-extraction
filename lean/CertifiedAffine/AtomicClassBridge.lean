import CertifiedAffine.CanonicalSort
import CertifiedAffine.GroupFrame

/-!
# Atomic Recognizer-to-Class Bridge

This module connects recognized single parity blocks to the declarative
`ParityEncoded.Class` atom constructor.  It intentionally does not claim that
canonical fingerprint equality alone implies literal-level syntactic
permutation; callers must supply that certificate, or use the stronger
syntactic recognition signal.
-/

namespace CertifiedAffine
namespace TseitinCNFData

namespace AtomicClassBridge

/-- A proof-carrying recognized parity CNF block is one declarative encoded atom. -/
theorem class_of_recognizedParityCNFBlock
    {m : Nat} (b : RecognizedParityCNFBlock m) :
    ParityEncoded.Class m b.blockCNF [b.compactGF2] := by
  unfold RecognizedParityCNFBlock.compactGF2
  exact ParityEncoded.Class.atom b.vars b.charge b.blockCNF b.block_perm

/-- A syntactically recognized parity block is one declarative encoded atom. -/
theorem class_of_syntacticRecognizedBlock
    {m : Nat} (b : SyntacticRecognizedParityBlock m) :
    ParityEncoded.Class m b.blockCNF [b.toRecognized.compactGF2] := by
  exact class_of_recognizedParityCNFBlock b.toRecognized

/--
A canonical-fingerprint block becomes a declarative atom once literal-level
permutation evidence is supplied.  This keeps the fingerprint recognizer's
current trust boundary explicit.
-/
theorem class_of_canonicalFingerprintRecognizedBlock_perm
    {m : Nat} (b : CanonicalFingerprintRecognizedParityBlock m)
    (hperm : List.Perm b.blockCNF b.spec.expandedCNF) :
    ParityEncoded.Class m b.blockCNF [b.compactGF2] := by
  unfold CanonicalFingerprintRecognizedParityBlock.compactGF2
  exact ParityEncoded.Class.atom b.spec.vars b.spec.charge b.blockCNF
    (by
      simpa [ParityBlockSyntacticSpec.expandedCNF] using hperm)

/--
A canonical-fingerprint block is a declarative atom when the stronger syntactic
permutation recognizer also accepts the same block/spec pair.
-/
theorem class_of_canonicalFingerprintRecognizedBlock_syntacticSignal
    {m : Nat} (b : CanonicalFingerprintRecognizedParityBlock m)
    (hsyntactic : parityBlockRecognitionSignal b.blockCNF b.spec = true) :
    ParityEncoded.Class m b.blockCNF [b.compactGF2] := by
  exact class_of_canonicalFingerprintRecognizedBlock_perm b
    (by
      simpa [ParityBlockSyntacticSpec.expandedCNF] using
        parityBlockRecognitionSignal_sound hsyntactic)

/--
The executable upgrade from a canonical-fingerprint block to a syntactic block
accepts exactly when the stronger syntactic recognizer has accepted the same
block/spec pair.
-/
theorem canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal
    {m : Nat} (b : CanonicalFingerprintRecognizedParityBlock m)
    (hsyntactic : parityBlockRecognitionSignal b.blockCNF b.spec = true) :
    b.toSyntactic?.isSome = true := by
  unfold CanonicalFingerprintRecognizedParityBlock.toSyntactic?
  simp [hsyntactic]

/--
Successful executable syntactic upgrade recovers the literal-level permutation
certificate that the declarative class bridge needs.
-/
theorem canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk
    {m : Nat} (b : CanonicalFingerprintRecognizedParityBlock m)
    (hsyntactic : b.toSyntactic?.isSome = true) :
    List.Perm b.blockCNF b.spec.expandedCNF := by
  unfold CanonicalFingerprintRecognizedParityBlock.toSyntactic? at hsyntactic
  by_cases hsignal : parityBlockRecognitionSignal b.blockCNF b.spec = true
  · exact parityBlockRecognitionSignal_sound hsignal
  · simp [hsignal] at hsyntactic

/-- Generated parity expansions recognize themselves syntactically. -/
theorem parityBlockRecognitionSignal_clausesForVertex_self
    {m : Nat}
    (vars : List (Fin m))
    (charge : Bool) :
    parityBlockRecognitionSignal
      (clausesForVertex vars charge)
      ({ vars := vars, charge := charge } :
        ParityBlockSyntacticSpec m) = true := by
  unfold parityBlockRecognitionSignal
  exact decide_eq_true (List.Perm.refl _)

/-- Clause permutations of generated parity expansions recognize syntactically. -/
theorem parityBlockRecognitionSignal_of_perm_clausesForVertex
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    (hperm : List.Perm f (clausesForVertex vars charge)) :
    parityBlockRecognitionSignal f
      ({ vars := vars, charge := charge } :
        ParityBlockSyntacticSpec m) = true := by
  unfold parityBlockRecognitionSignal
  exact decide_eq_true
    (by
      simpa [ParityBlockSyntacticSpec.expandedCNF] using hperm)

/-- Generated parity expansions also recognize themselves by canonical fingerprints. -/
theorem canonicalParityBlockRecognitionSignal_clausesForVertex_self
    {m : Nat}
    (vars : List (Fin m))
    (charge : Bool) :
    canonicalParityBlockRecognitionSignal
      (clausesForVertex vars charge)
      ({ vars := vars, charge := charge } :
        ParityBlockSyntacticSpec m) = true := by
  unfold canonicalParityBlockRecognitionSignal
  exact decide_eq_true rfl

/-- Membership in a sorted canonical block fingerprint is membership in the mapped clauses. -/
theorem mem_canonicalBlockFingerprint_iff
    {m : Nat}
    {fingerprint : List Nat}
    {f : CNFModel.CNF m} :
    List.Mem fingerprint (canonicalBlockFingerprint f) <->
      exists c : CNFModel.Clause m,
        List.Mem c f /\ canonicalClauseFingerprint c = fingerprint := by
  unfold canonicalBlockFingerprint sortClauseFingerprints
  rw [GroupFrame.mem_sortByBool_iff]
  constructor
  · intro hmem
    exact List.mem_map.1 hmem
  · intro hmem
    rcases hmem with ⟨c, hc, hfp⟩
    exact List.mem_map.2 ⟨c, hc, hfp⟩

/-- Canonical clause-fingerprint sorting preserves the count of each fingerprint. -/
theorem sortClauseFingerprints_count_eq
    (fingerprint : List Nat) (fingerprints : List (List Nat)) :
    (sortClauseFingerprints fingerprints).count fingerprint =
      fingerprints.count fingerprint := by
  unfold sortClauseFingerprints
  have hfun :
      natListLexLE =
        (fun a b : List Nat => decide (NatListLexLEProp a b)) := by
    funext a b
    exact natListLexLE_eq_decide_prop a b
  rw [hfun, sortByBool_decide_eq_insertionSort (r := NatListLexLEProp)]
  unfold List.count
  exact List.Perm.countP_eq (fun x => x == fingerprint)
    (List.perm_insertionSort NatListLexLEProp fingerprints)

/-- Canonical block-fingerprint membership distributes over CNF append. -/
theorem mem_canonicalBlockFingerprint_append_iff
    {m : Nat}
    {fingerprint : List Nat}
    {f g : CNFModel.CNF m} :
    List.Mem fingerprint (canonicalBlockFingerprint (f ++ g)) <->
      List.Mem fingerprint (canonicalBlockFingerprint f) \/
        List.Mem fingerprint (canonicalBlockFingerprint g) := by
  rw [mem_canonicalBlockFingerprint_iff]
  constructor
  · intro hmem
    rcases hmem with ⟨c, hc, hfp⟩
    rcases List.mem_append.1 hc with hf | hg
    · exact Or.inl
        (mem_canonicalBlockFingerprint_iff.2 ⟨c, hf, hfp⟩)
    · exact Or.inr
        (mem_canonicalBlockFingerprint_iff.2 ⟨c, hg, hfp⟩)
  · intro hmem
    rcases hmem with hf | hg
    · rcases mem_canonicalBlockFingerprint_iff.1 hf with ⟨c, hc, hfp⟩
      exact ⟨c, List.mem_append.2 (Or.inl hc), hfp⟩
    · rcases mem_canonicalBlockFingerprint_iff.1 hg with ⟨c, hc, hfp⟩
      exact ⟨c, List.mem_append.2 (Or.inr hc), hfp⟩

/-- Canonical block-fingerprint counts distribute over CNF append. -/
theorem canonicalBlockFingerprint_count_append
    {m : Nat}
    (fingerprint : List Nat)
    (f g : CNFModel.CNF m) :
    (canonicalBlockFingerprint (f ++ g)).count fingerprint =
      (canonicalBlockFingerprint f).count fingerprint +
        (canonicalBlockFingerprint g).count fingerprint := by
  unfold canonicalBlockFingerprint
  rw [sortClauseFingerprints_count_eq]
  rw [List.map_append, List.count_append]
  rw [← sortClauseFingerprints_count_eq fingerprint
    (f.map canonicalClauseFingerprint)]
  rw [← sortClauseFingerprints_count_eq fingerprint
    (g.map canonicalClauseFingerprint)]

/-- A clause contributes its canonical fingerprint to the containing block fingerprint. -/
theorem canonicalClauseFingerprint_mem_canonicalBlockFingerprint_of_mem
    {m : Nat}
    {f : CNFModel.CNF m}
    {c : CNFModel.Clause m}
    (hmem : List.Mem c f) :
    List.Mem (canonicalClauseFingerprint c) (canonicalBlockFingerprint f) := by
  exact mem_canonicalBlockFingerprint_iff.2
    ⟨c, hmem, rfl⟩

/-- Membership in a sorted canonical clause fingerprint is membership in the mapped literals. -/
theorem mem_canonicalClauseFingerprint_iff
    {m : Nat}
    {atom : Nat}
    {c : CNFModel.Clause m} :
    List.Mem atom (canonicalClauseFingerprint c) <->
      exists l : CNFModel.Literal m,
        List.Mem l c /\ canonicalLiteralAtom l = atom := by
  unfold canonicalClauseFingerprint sortNatFingerprintAtoms
  rw [GroupFrame.mem_sortByBool_iff]
  constructor
  · intro hmem
    exact List.mem_map.1 hmem
  · intro hmem
    rcases hmem with ⟨l, hl, hfp⟩
    exact List.mem_map.2 ⟨l, hl, hfp⟩

/-- A literal in the all-false assignment clause is always positive. -/
theorem literal_sign_true_of_mem_clauseForAssignment_replicate_false
    {m : Nat}
    {l : CNFModel.Literal m} :
    forall (vars : List (Fin m)),
      List.Mem l
        (clauseForAssignment vars (List.replicate vars.length false)) ->
        l.sign = true := by
  intro vars
  induction vars with
  | nil =>
      intro hmem
      cases hmem
  | cons v vars ih =>
      intro hmem
      change
        List.Mem l
          (({ var := v, sign := true } : CNFModel.Literal m) ::
            clauseForAssignment vars
              (List.replicate vars.length false)) at hmem
      cases hmem with
      | head =>
          rfl
      | tail _ htail =>
          exact ih htail

/-- Even signed-literal atoms cannot occur in the all-false assignment clause. -/
theorem evenLiteralAtom_not_mem_canonicalClauseFingerprint_allFalse
    {m : Nat}
    (vars : List (Fin m))
    (v : Fin m) :
    Not
      (List.Mem (2 * v.val)
        (canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false)))) := by
  intro hmem
  rcases mem_canonicalClauseFingerprint_iff.1 hmem with ⟨l, hl, hfp⟩
  have hsign :
      l.sign = true :=
    literal_sign_true_of_mem_clauseForAssignment_replicate_false vars hl
  have hatom : 2 * l.var.val + 1 = 2 * v.val := by
    simpa [canonicalLiteralAtom, hsign] using hfp
  omega

/-- A Boolean list with true parity contains at least one true bit. -/
theorem true_mem_of_parity_true :
    forall {bs : List Bool}, parity bs = true -> List.Mem true bs := by
  intro bs
  induction bs with
  | nil =>
      intro hpar
      simp [parity] at hpar
  | cons b bs ih =>
      intro hpar
      cases b with
      | false =>
          have htail : parity bs = true := by
            simpa [parity_cons] using hpar
          exact List.Mem.tail false (ih htail)
      | true =>
          exact List.Mem.head bs

/--
A row containing a true bit contributes at least one even signed-literal atom
to the canonical fingerprint of its forbidden assignment clause.
-/
theorem exists_evenLiteralAtom_mem_canonicalClauseFingerprint_clauseForAssignment
    {m : Nat} :
    forall {vars : List (Fin m)} {bs : List Bool},
      bs.length = vars.length ->
      List.Mem true bs ->
      exists v : Fin m,
        List.Mem (2 * v.val)
          (canonicalClauseFingerprint (clauseForAssignment vars bs)) := by
  intro vars
  induction vars with
  | nil =>
      intro bs hlen htrue
      cases bs with
      | nil =>
          cases htrue
      | cons b bs =>
          cases hlen
  | cons v vars ih =>
      intro bs hlen htrue
      cases bs with
      | nil =>
          cases hlen
      | cons b bs =>
          have htailLen : bs.length = vars.length := Nat.succ.inj hlen
          cases b with
          | false =>
              have htailTrue : List.Mem true bs := by
                cases htrue with
                | tail _ htail =>
                    exact htail
              rcases ih htailLen htailTrue with ⟨w, hw⟩
              rcases mem_canonicalClauseFingerprint_iff.1 hw with
                ⟨l, hl, hfp⟩
              refine ⟨w, mem_canonicalClauseFingerprint_iff.2 ?_⟩
              refine ⟨l, ?_, hfp⟩
              simpa [clauseForAssignment] using List.Mem.tail
                ({ var := v, sign := true } : CNFModel.Literal m) hl
          | true =>
              refine ⟨v, mem_canonicalClauseFingerprint_iff.2 ?_⟩
              refine
                ⟨({ var := v, sign := false } : CNFModel.Literal m), ?_, ?_⟩
              · change
                  List.Mem
                    ({ var := v, sign := false } : CNFModel.Literal m)
                    (({ var := v, sign := false } : CNFModel.Literal m) ::
                      clauseForAssignment vars bs)
                exact List.Mem.head (clauseForAssignment vars bs)
              · simp [canonicalLiteralAtom]

/-- A fingerprint present on one side and absent on the other separates block fingerprints. -/
theorem canonicalBlockFingerprint_ne_of_mem_not_mem
    {m : Nat}
    {source target : CNFModel.CNF m}
    {fingerprint : List Nat}
    (hsource : List.Mem fingerprint (canonicalBlockFingerprint source))
    (htarget :
      Not (List.Mem fingerprint (canonicalBlockFingerprint target))) :
    Not (canonicalBlockFingerprint source =
      canonicalBlockFingerprint target) := by
  intro heq
  exact htarget (by simpa [heq] using hsource)

/-- The all-false Boolean row has even parity. -/
theorem parity_replicate_false (n : Nat) :
    parity (List.replicate n false) = false := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate, parity_cons, ih]

/--
The all-false assignment clause is always present in the true-charge generated
parity block, because it has false parity.
-/
theorem allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true
    {m : Nat}
    (vars : List (Fin m)) :
    List.Mem
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false)))
      (canonicalBlockFingerprint (clausesForVertex vars true)) := by
  apply canonicalClauseFingerprint_mem_canonicalBlockFingerprint_of_mem
  apply clauseForAssignment_mem_clausesForVertex_of_bad_parity
  · simp
  · simp [parity_replicate_false]

/--
The generated true/false block-fingerprint inequality follows once the
all-false assignment fingerprint is known to be absent from the false-charge
block.
-/
theorem canonicalBlockFingerprint_clausesForVertex_true_false_ne_of_allFalseFingerprint_not_mem
    {m : Nat}
    {vars : List (Fin m)}
    (hnot :
      Not
        (List.Mem
          (canonicalClauseFingerprint
            (clauseForAssignment vars (List.replicate vars.length false)))
          (canonicalBlockFingerprint (clausesForVertex vars false)))) :
    Not
      (canonicalBlockFingerprint (clausesForVertex vars true) =
        canonicalBlockFingerprint (clausesForVertex vars false)) := by
  exact
    canonicalBlockFingerprint_ne_of_mem_not_mem
      (allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true
        vars)
      hnot

/--
The all-false assignment fingerprint is absent from the generated false-charge
block: every clause in that block comes from an odd row and therefore has at
least one even signed-literal atom, while the all-false clause has none.
-/
theorem allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false
    {m : Nat}
    (vars : List (Fin m)) :
    Not
      (List.Mem
        (canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false)))
        (canonicalBlockFingerprint (clausesForVertex vars false))) := by
  intro hmem
  rcases mem_canonicalBlockFingerprint_iff.1 hmem with ⟨c, hc, hfp⟩
  rcases mem_clausesForVertex_imp_exists_bad_row hc with
    ⟨bs, hlen, hbad, hcEq⟩
  subst c
  have hpar : parity bs = true := by
    cases hp : parity bs with
    | false =>
        simp [hp] at hbad
    | true =>
        rfl
  have htrue : List.Mem true bs := true_mem_of_parity_true hpar
  rcases
    exists_evenLiteralAtom_mem_canonicalClauseFingerprint_clauseForAssignment
      hlen htrue with
    ⟨v, heven⟩
  have hallFalseMem :
      List.Mem (2 * v.val)
        (canonicalClauseFingerprint
          (clauseForAssignment vars
            (List.replicate vars.length false))) := by
    simpa [hfp] using heven
  exact
    evenLiteralAtom_not_mem_canonicalClauseFingerprint_allFalse vars v
      hallFalseMem

/-- Generated true- and false-charge parity blocks have different block fingerprints. -/
theorem canonicalBlockFingerprint_clausesForVertex_true_false_ne
    {m : Nat}
    (vars : List (Fin m)) :
    Not
      (canonicalBlockFingerprint (clausesForVertex vars true) =
        canonicalBlockFingerprint (clausesForVertex vars false)) := by
  exact
    canonicalBlockFingerprint_clausesForVertex_true_false_ne_of_allFalseFingerprint_not_mem
      (allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false
        vars)

/--
The all-false assignment fingerprint is a charge witness for generated parity
blocks: it appears exactly in true-charge generated blocks.
-/
theorem allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_iff_charge
    {m : Nat}
    (vars : List (Fin m)) (charge : Bool) :
    List.Mem
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false)))
      (canonicalBlockFingerprint (clausesForVertex vars charge)) ↔
      charge = true := by
  cases charge
  · constructor
    · intro hmem
      exact False.elim
        ((allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false
          vars) hmem)
    · intro hcharge
      cases hcharge
  · constructor
    · intro _hmem
      rfl
    · intro _hcharge
      exact
        allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true
          vars

/--
Executable Boolean form of the all-false fingerprint charge witness.
-/
theorem allFalseClauseFingerprint_signal_clausesForVertex_eq_charge
    {m : Nat}
    (vars : List (Fin m)) (charge : Bool) :
    (canonicalBlockFingerprint (clausesForVertex vars charge)).contains
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false))) =
      charge := by
  cases charge
  · have hnot :=
      allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false
        vars
    cases hcontains :
        (canonicalBlockFingerprint (clausesForVertex vars false)).contains
          (canonicalClauseFingerprint
            (clauseForAssignment vars (List.replicate vars.length false))) with
    | false =>
        rfl
    | true =>
        have hmem :
            List.Mem
              (canonicalClauseFingerprint
                (clauseForAssignment vars (List.replicate vars.length false)))
              (canonicalBlockFingerprint (clausesForVertex vars false)) :=
          List.elem_iff.mp (by simpa [List.contains] using hcontains)
        exact False.elim (hnot hmem)
  · have hmem :=
      allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true
        vars
    simpa [List.contains] using (List.elem_iff.mpr hmem)

/--
False-charge generated blocks contribute no all-false clause fingerprints.
-/
theorem allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_false
    {m : Nat}
    (vars : List (Fin m)) :
    (canonicalBlockFingerprint (clausesForVertex vars false)).count
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false))) = 0 := by
  exact List.count_eq_zero_of_not_mem
    (allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false
      vars)

/--
True-charge generated blocks contribute at least one all-false clause
fingerprint.
-/
theorem one_le_allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true
    {m : Nat}
    (vars : List (Fin m)) :
    1 <=
      (canonicalBlockFingerprint (clausesForVertex vars true)).count
        (canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false))) := by
  exact Nat.succ_le_of_lt
    (List.count_pos_iff.2
      (allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true
        vars))

/--
Within one generated parity block, the all-false canonical fingerprint can only
come from the all-false row.
-/
theorem row_eq_replicate_false_of_canonicalClauseFingerprint_eq_allFalse
    {m : Nat} {vars : List (Fin m)} {bs : List Bool}
    (hlen : bs.length = vars.length)
    (hfp :
      canonicalClauseFingerprint (clauseForAssignment vars bs) =
        canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false))) :
    bs = List.replicate vars.length false := by
  have hnot : Not (List.Mem true bs) := by
    intro htrue
    cases exists_evenLiteralAtom_mem_canonicalClauseFingerprint_clauseForAssignment
        (vars := vars) (bs := bs) hlen htrue with
    | intro v heven =>
        have hallFalseMem :
            List.Mem (2 * v.val)
              (canonicalClauseFingerprint
                (clauseForAssignment vars (List.replicate vars.length false))) := by
          simpa [hfp] using heven
        exact evenLiteralAtom_not_mem_canonicalClauseFingerprint_allFalse
          vars v hallFalseMem
  have hrow := boolList_eq_replicate_false_of_true_not_mem bs hnot
  calc
    bs = List.replicate bs.length false := hrow
    _ = List.replicate vars.length false := by rw [hlen]

/--
The all-false fingerprint identifies the all-false generated clause in a
true-charge parity block.
-/
theorem clause_eq_allFalse_of_mem_clausesForVertex_true_and_fingerprint_eq
    {m : Nat} {vars : List (Fin m)} {c : CNFModel.Clause m}
    (hmem : List.Mem c (clausesForVertex vars true))
    (hfp :
      canonicalClauseFingerprint c =
        canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false))) :
    c = clauseForAssignment vars (List.replicate vars.length false) := by
  cases mem_clausesForVertex_imp_exists_bad_row hmem with
  | intro bs hwit =>
      cases hwit with
      | intro hlen hrest =>
          cases hrest with
          | intro _hbad hc =>
              have hfp' :
                  canonicalClauseFingerprint (clauseForAssignment vars bs) =
                    canonicalClauseFingerprint
                      (clauseForAssignment vars
                        (List.replicate vars.length false)) := by
                simpa [hc] using hfp
              rw [hc]
              rw [
                row_eq_replicate_false_of_canonicalClauseFingerprint_eq_allFalse
                  (vars := vars) (bs := bs) hlen hfp']

private theorem allFalseClauseFingerprint_count_foldl_true_aux
    {m : Nat} (vars : List (Fin m)) :
    forall (rows : List (List Bool)) (acc : CNFModel.CNF m),
      (forall bs, List.Mem bs rows -> bs.length = vars.length) ->
      (((rows.foldl
          (fun acc bs =>
            if parity bs = true then acc else acc ++ [clauseForAssignment vars bs])
          acc).map canonicalClauseFingerprint).count
        (canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false)))) =
        ((acc.map canonicalClauseFingerprint).count
          (canonicalClauseFingerprint
            (clauseForAssignment vars (List.replicate vars.length false)))) +
          rows.count (List.replicate vars.length false) := by
  intro rows
  induction rows with
  | nil =>
      intro acc _hlen
      simp
  | cons row rows ih =>
      intro acc hlen
      have htailLen :
          forall bs, List.Mem bs rows -> bs.length = vars.length := by
        intro bs hmem
        exact hlen bs (List.Mem.tail row hmem)
      have hrowLen : row.length = vars.length :=
        hlen row (List.Mem.head rows)
      by_cases hpar : parity row = true
      case pos =>
        have hrowNe : Not (row = List.replicate vars.length false) := by
          intro heq
          have hpf : parity row = false := by
            simpa [heq] using parity_replicate_false vars.length
          rw [hpf] at hpar
          contradiction
        have hrowBeq :
            (row == List.replicate vars.length false) = false :=
          (beq_eq_false_iff_ne).2 hrowNe
        have hih := ih acc htailLen
        simp [hpar]
        rw [hih]
        simp [List.count_cons, hrowBeq]
      case neg =>
        by_cases hrowEq : row = List.replicate vars.length false
        case pos =>
          have hih := ih (acc ++ [clauseForAssignment vars row]) htailLen
          simp [hpar]
          rw [hih]
          rw [List.map_append, List.count_append]
          simp [hrowEq, List.count_cons]
          omega
        case neg =>
          have hfpNe :
              Not
                (canonicalClauseFingerprint (clauseForAssignment vars row) =
                  canonicalClauseFingerprint
                    (clauseForAssignment vars
                      (List.replicate vars.length false))) := by
            intro hfp
            have hrowAll :=
              row_eq_replicate_false_of_canonicalClauseFingerprint_eq_allFalse
                (vars := vars) (bs := row) hrowLen hfp
            exact hrowEq hrowAll
          have hfpBeq :
              (canonicalClauseFingerprint (clauseForAssignment vars row) ==
                canonicalClauseFingerprint
                  (clauseForAssignment vars
                    (List.replicate vars.length false))) = false :=
            (beq_eq_false_iff_ne).2 hfpNe
          have hrowBeq :
              (row == List.replicate vars.length false) = false :=
            (beq_eq_false_iff_ne).2 hrowEq
          have hih := ih (acc ++ [clauseForAssignment vars row]) htailLen
          simp [hpar]
          rw [hih]
          rw [List.map_append, List.count_append]
          simp [List.count_cons, hfpBeq, hrowBeq]

/--
True-charge generated blocks contribute exactly one all-false clause
fingerprint.
-/
theorem allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true_eq_one
    {m : Nat}
    (vars : List (Fin m)) :
    (canonicalBlockFingerprint (clausesForVertex vars true)).count
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false))) = 1 := by
  unfold canonicalBlockFingerprint
  rw [sortClauseFingerprints_count_eq]
  unfold clausesForVertex
  have hfold :=
    allFalseClauseFingerprint_count_foldl_true_aux vars
      (allAssignments vars.length) []
      (by
        intro bs hmem
        exact length_of_mem_allAssignments hmem)
  simpa [Bool.beq_eq_decide_eq, allAssignments_count_replicate_false] using hfold

/-- A canonical parity-block signal is false when the block fingerprints differ. -/
theorem canonicalParityBlockRecognitionSignal_eq_false_of_fingerprint_ne
    {m : Nat}
    {blockCNF : CNFModel.CNF m}
    {spec : ParityBlockSyntacticSpec m}
    (hne :
      Not
        (canonicalBlockFingerprint blockCNF =
          canonicalBlockFingerprint spec.expandedCNF)) :
    canonicalParityBlockRecognitionSignal blockCNF spec = false := by
  unfold canonicalParityBlockRecognitionSignal
  simp [hne]

/--
For generated true-charge blocks, the false-charge canonical signal is false
once the true- and false-charge canonical block fingerprints are known to
differ.
-/
theorem canonicalParityBlockRecognitionSignal_clausesForVertex_true_false_eq_false_of_fingerprint_ne
    {m : Nat}
    {vars : List (Fin m)}
    (hne :
      Not
        (canonicalBlockFingerprint (clausesForVertex vars true) =
          canonicalBlockFingerprint (clausesForVertex vars false))) :
    canonicalParityBlockRecognitionSignal
      (clausesForVertex vars true)
      ({ vars := vars, charge := false } :
        ParityBlockSyntacticSpec m) = false := by
  apply canonicalParityBlockRecognitionSignal_eq_false_of_fingerprint_ne
  simpa [ParityBlockSyntacticSpec.expandedCNF] using hne

/--
If the executable support inference recovers the same variable list used to
generate a parity expansion, the one-charge canonical recognizer returns a
block and that block passes the executable syntactic-upgrade check.
-/
theorem inferCanonicalParityBlockWithCharge_clausesForVertex_self_toSyntactic
    {m : Nat}
    (vars : List (Fin m))
    (charge : Bool)
    (hsupport :
      parityCandidateCanonicalSupportFromBlock
        (clausesForVertex vars charge) = vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlockWithCharge
          (clausesForVertex vars charge) charge = some block /\
        block.toSyntactic?.isSome = true := by
  let block : CanonicalFingerprintRecognizedParityBlock m :=
    { blockCNF := clausesForVertex vars charge
      spec := { vars := vars, charge := charge }
      fingerprintSignal :=
        canonicalParityBlockRecognitionSignal_clausesForVertex_self vars charge }
  refine Exists.intro block ?_
  constructor
  · unfold inferCanonicalParityBlockWithCharge inferredCanonicalParityBlockSpec
    simp [hsupport, block,
      canonicalParityBlockRecognitionSignal_clausesForVertex_self]
  · exact
      canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal
        block
        (parityBlockRecognitionSignal_clausesForVertex_self vars charge)

/--
For a nonempty generated parity expansion whose variable list is already in
canonical support order, the one-charge executable canonical recognizer returns
a block and the block passes `toSyntactic?`.
-/
theorem inferCanonicalParityBlockWithCharge_clausesForVertex_normal_toSyntactic
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlockWithCharge
          (clausesForVertex vars charge) charge = some block /\
        block.toSyntactic?.isSome = true := by
  exact
    inferCanonicalParityBlockWithCharge_clausesForVertex_self_toSyntactic
      vars charge
      (GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal
        (m := m) (vars := vars) (charge := charge) hcnf hnormal)

/--
For any nonempty clause permutation of a generated parity expansion in
canonical support order, the one-charge executable canonical recognizer returns
the expected block once the canonical fingerprint signal has been supplied.
This isolates the remaining hard obligation as fingerprint invariance under
clause permutation.
-/
theorem inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := charge } :
          ParityBlockSyntacticSpec m) = true) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlockWithCharge f charge = some block /\
        block.toSyntactic?.isSome = true /\
        block.compactGF2 = parityClauseForVertex vars charge := by
  let block : CanonicalFingerprintRecognizedParityBlock m :=
    { blockCNF := f
      spec := { vars := vars, charge := charge }
      fingerprintSignal := hsignal }
  refine ⟨block, ?_, ?_, ?_⟩
  · unfold inferCanonicalParityBlockWithCharge inferredCanonicalParityBlockSpec
    have hsupport :
        parityCandidateCanonicalSupportFromBlock f = vars :=
      GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_perm_clausesForVertex_normal
        hperm hf hnormal
    simp [hsupport, hsignal, block]
  · exact
      canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal
        block
        (parityBlockRecognitionSignal_of_perm_clausesForVertex hperm)
  · rfl

/--
False-charge generated atoms are direct for the public two-charge recognizer:
the recognizer tries `false` first.  The only remaining supplied executable
premise is the canonical fingerprint signal for the permuted atom.
-/
theorem inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal_of_signal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = true) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock f = some block /\
        block.toSyntactic?.isSome = true /\
        block.compactGF2 = parityClauseForVertex vars false := by
  rcases
    inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal
      hperm hf hnormal hsignal with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  refine ⟨block, ?_, hsyntactic, hcompact⟩
  unfold inferCanonicalParityBlock
  rw [hinfer]

/--
True-charge generated atoms are recognized by the public two-charge recognizer
once the preceding false-charge attempt is known to miss.  The positive signal
premise is exactly the remaining canonical fingerprint obligation for the true
block.
-/
theorem inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal_of_signal_of_falseMiss
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := true } :
          ParityBlockSyntacticSpec m) = true)
    (hmiss : inferCanonicalParityBlockWithCharge f false = none) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock f = some block /\
        block.toSyntactic?.isSome = true /\
        block.compactGF2 = parityClauseForVertex vars true := by
  rcases
    inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal
      hperm hf hnormal hsignal with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  refine ⟨block, ?_, hsyntactic, hcompact⟩
  unfold inferCanonicalParityBlock
  rw [hmiss, hinfer]

/--
For any nonempty clause permutation of a generated parity expansion in
canonical support order, the one-charge executable canonical recognizer returns
the expected block.  The canonical fingerprint signal is discharged by the
generic sort/fingerprint permutation-invariance theorem.
-/
theorem inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlockWithCharge f charge = some block /\
        block.toSyntactic?.isSome = true /\
        block.compactGF2 = parityClauseForVertex vars charge := by
  have hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := charge } :
          ParityBlockSyntacticSpec m) = true :=
    canonicalParityBlockRecognitionSignal_of_perm
      (by simpa [ParityBlockSyntacticSpec.expandedCNF] using hperm)
  exact
    inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal
      hperm hf hnormal hsignal

/--
For true-charge generated clause permutations, testing the permuted block
against the false-charge spec is rejected.  This transports the existing
true/false generated fingerprint separation across the candidate permutation.
-/
theorem canonicalParityBlockRecognitionSignal_perm_clausesForVertex_true_false_eq_false
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    (hperm : List.Perm f (clausesForVertex vars true)) :
    canonicalParityBlockRecognitionSignal f
      ({ vars := vars, charge := false } :
        ParityBlockSyntacticSpec m) = false := by
  apply canonicalParityBlockRecognitionSignal_eq_false_of_fingerprint_ne
  intro hfp
  have htrue :
      canonicalBlockFingerprint f =
        canonicalBlockFingerprint (clausesForVertex vars true) :=
    canonicalBlockFingerprint_eq_of_perm hperm
  have htarget :
      canonicalBlockFingerprint (clausesForVertex vars true) =
        canonicalBlockFingerprint (clausesForVertex vars false) := by
    rw [htrue.symm]
    simpa [ParityBlockSyntacticSpec.expandedCNF] using hfp
  exact (canonicalBlockFingerprint_clausesForVertex_true_false_ne vars) htarget

/--
False-charge generated atom permutations are direct for the public recognizer:
the recognizer tries false first, and the canonical signal is now discharged by
generic fingerprint permutation invariance.
-/
theorem inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock f = some block /\
        block.toSyntactic?.isSome = true /\
        block.compactGF2 = parityClauseForVertex vars false := by
  have hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = true :=
    canonicalParityBlockRecognitionSignal_of_perm
      (by simpa [ParityBlockSyntacticSpec.expandedCNF] using hperm)
  exact
    inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal_of_signal
      hperm hf hnormal hsignal

/--
True-charge generated atom permutations pass the public recognizer without
caller-supplied signal or false-miss premises.  The positive signal follows
from canonical fingerprint permutation invariance, and the false-first miss
follows from transported true/false fingerprint separation.
-/
theorem inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock f = some block /\
        block.toSyntactic?.isSome = true /\
        block.compactGF2 = parityClauseForVertex vars true := by
  have hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := true } :
          ParityBlockSyntacticSpec m) = true :=
    canonicalParityBlockRecognitionSignal_of_perm
      (by simpa [ParityBlockSyntacticSpec.expandedCNF] using hperm)
  have hfalseSignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = false :=
    canonicalParityBlockRecognitionSignal_perm_clausesForVertex_true_false_eq_false
      hperm
  have hsupport :
      parityCandidateCanonicalSupportFromBlock f = vars :=
    GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_perm_clausesForVertex_normal
      hperm hf hnormal
  have hfalseSignalInferred :
      canonicalParityBlockRecognitionSignal f
        (inferredCanonicalParityBlockSpec f false) = false := by
    unfold inferredCanonicalParityBlockSpec
    rw [hsupport]
    exact hfalseSignal
  have hmiss : inferCanonicalParityBlockWithCharge f false = none :=
    by
      unfold inferCanonicalParityBlockWithCharge
      simp [hfalseSignalInferred]
  exact
    inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal_of_signal_of_falseMiss
      hperm hf hnormal hsignal hmiss

/--
For a nonempty generated false-charge parity expansion in canonical support
order, the public two-charge recognizer returns a block and that block passes
`toSyntactic?`.  This case is direct because the recognizer tries `false`
first.
-/
theorem inferCanonicalParityBlock_clausesForVertex_false_normal_toSyntactic
    {m : Nat}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars false = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock
          (clausesForVertex vars false) = some block /\
        block.toSyntactic?.isSome = true := by
  have hres :=
    inferCanonicalParityBlockWithCharge_clausesForVertex_normal_toSyntactic
      (m := m) (vars := vars) (charge := false) hcnf hnormal
  cases hres with
  | intro block hblock =>
      refine Exists.intro block ?_
      exact And.intro
        (by
          unfold inferCanonicalParityBlock
          rw [hblock.1])
        hblock.2

/--
A one-charge canonical recognizer misses whenever its inferred canonical
fingerprint signal is explicitly false.
-/
theorem inferCanonicalParityBlockWithCharge_eq_none_of_signal_false
    {m : Nat}
    {blockCNF : CNFModel.CNF m}
    {charge : Bool}
    (hsignal :
      canonicalParityBlockRecognitionSignal blockCNF
        (inferredCanonicalParityBlockSpec blockCNF charge) = false) :
    inferCanonicalParityBlockWithCharge blockCNF charge = none := by
  unfold inferCanonicalParityBlockWithCharge
  simp [hsignal]

/--
For a generated true-charge parity expansion in canonical support order, a
false canonical signal for the corresponding false-charge spec is enough to
prove that the public recognizer's first, false-charge attempt misses.
-/
theorem inferCanonicalParityBlockWithCharge_clausesForVertex_true_false_eq_none_of_signal_false
    {m : Nat}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars true = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal
        (clausesForVertex vars true)
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = false) :
    inferCanonicalParityBlockWithCharge
        (clausesForVertex vars true) false = none := by
  apply inferCanonicalParityBlockWithCharge_eq_none_of_signal_false
  have hsupport :=
    GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal
      (m := m) (vars := vars) (charge := true) hcnf hnormal
  simpa [inferredCanonicalParityBlockSpec, hsupport] using hsignal

/--
For a nonempty generated true-charge parity expansion in canonical support
order, the public two-charge recognizer returns a syntactically upgradable
block once the false-charge attempt is known to miss.  The remaining premise is
the exact false-first ordering obligation.
-/
theorem inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseMiss
    {m : Nat}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars true = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hmiss :
      inferCanonicalParityBlockWithCharge
          (clausesForVertex vars true) false = none) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock
          (clausesForVertex vars true) = some block /\
        block.toSyntactic?.isSome = true := by
  have hres :=
    inferCanonicalParityBlockWithCharge_clausesForVertex_normal_toSyntactic
      (m := m) (vars := vars) (charge := true) hcnf hnormal
  cases hres with
  | intro block hblock =>
      refine Exists.intro block ?_
      exact And.intro
        (by
          unfold inferCanonicalParityBlock
          rw [hmiss]
          exact hblock.1)
        hblock.2

/--
For a nonempty generated true-charge parity expansion in canonical support
order, the public two-charge recognizer returns a syntactically upgradable
block once the corresponding false-charge canonical fingerprint signal is known
to be false.
-/
theorem inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseSignal
    {m : Nat}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars true = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal
        (clausesForVertex vars true)
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = false) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock
          (clausesForVertex vars true) = some block /\
        block.toSyntactic?.isSome = true := by
  exact
    inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseMiss
      hcnf hnormal
      (inferCanonicalParityBlockWithCharge_clausesForVertex_true_false_eq_none_of_signal_false
        hcnf hnormal hsignal)

/--
For a nonempty generated true-charge parity expansion in canonical support
order, the public two-charge recognizer returns a syntactically upgradable
block once the true- and false-charge generated block fingerprints are known to
differ.
-/
theorem inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_fingerprint_ne
    {m : Nat}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars true = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hne :
      Not
        (canonicalBlockFingerprint (clausesForVertex vars true) =
          canonicalBlockFingerprint (clausesForVertex vars false))) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock
          (clausesForVertex vars true) = some block /\
        block.toSyntactic?.isSome = true := by
  exact
    inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseSignal
      hcnf hnormal
      (canonicalParityBlockRecognitionSignal_clausesForVertex_true_false_eq_false_of_fingerprint_ne
        hne)

/--
For a nonempty generated true-charge parity expansion in canonical support
order, the public two-charge recognizer returns a syntactically upgradable
block.  The proof now discharges the false-first miss by a generated
true/false fingerprint separation.
-/
theorem inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic
    {m : Nat}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars true = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock
          (clausesForVertex vars true) = some block /\
        block.toSyntactic?.isSome = true := by
  exact
    inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_fingerprint_ne
      hcnf hnormal
      (canonicalBlockFingerprint_clausesForVertex_true_false_ne vars)

/--
For a nonempty generated parity expansion in canonical support order, the
public two-charge recognizer returns a syntactically upgradable block for
either charge, and its compact GF(2) equation is exactly the generated parity
equation.
-/
theorem inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock
          (clausesForVertex vars charge) = some block /\
        block.toSyntactic?.isSome = true /\
        block.compactGF2 = parityClauseForVertex vars charge := by
  cases charge with
  | false =>
      let block : CanonicalFingerprintRecognizedParityBlock m :=
        { blockCNF := clausesForVertex vars false
          spec := { vars := vars, charge := false }
          fingerprintSignal :=
            canonicalParityBlockRecognitionSignal_clausesForVertex_self vars false }
      have hsupport :
          parityCandidateCanonicalSupportFromBlock
            (clausesForVertex vars false) = vars :=
        GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal
          (m := m) (vars := vars) (charge := false) hcnf hnormal
      have hwith :
          inferCanonicalParityBlockWithCharge
            (clausesForVertex vars false) false = some block := by
        unfold inferCanonicalParityBlockWithCharge inferredCanonicalParityBlockSpec
        simp [hsupport, block,
          canonicalParityBlockRecognitionSignal_clausesForVertex_self]
      refine ⟨block, ?_, ?_, ?_⟩
      · unfold inferCanonicalParityBlock
        rw [hwith]
      · exact
          canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal
            block
            (parityBlockRecognitionSignal_clausesForVertex_self vars false)
      · rfl
  | true =>
      let block : CanonicalFingerprintRecognizedParityBlock m :=
        { blockCNF := clausesForVertex vars true
          spec := { vars := vars, charge := true }
          fingerprintSignal :=
            canonicalParityBlockRecognitionSignal_clausesForVertex_self vars true }
      have hsupport :
          parityCandidateCanonicalSupportFromBlock
            (clausesForVertex vars true) = vars :=
        GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal
          (m := m) (vars := vars) (charge := true) hcnf hnormal
      have hmiss :
          inferCanonicalParityBlockWithCharge
            (clausesForVertex vars true) false = none :=
        inferCanonicalParityBlockWithCharge_clausesForVertex_true_false_eq_none_of_signal_false
          hcnf hnormal
          (canonicalParityBlockRecognitionSignal_clausesForVertex_true_false_eq_false_of_fingerprint_ne
            (canonicalBlockFingerprint_clausesForVertex_true_false_ne vars))
      have hwith :
          inferCanonicalParityBlockWithCharge
            (clausesForVertex vars true) true = some block := by
        unfold inferCanonicalParityBlockWithCharge inferredCanonicalParityBlockSpec
        simp [hsupport, block,
          canonicalParityBlockRecognitionSignal_clausesForVertex_self]
      refine ⟨block, ?_, ?_, ?_⟩
      · unfold inferCanonicalParityBlock
        rw [hmiss]
        exact hwith
      · exact
          canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal
            block
            (parityBlockRecognitionSignal_clausesForVertex_self vars true)
      · rfl

/--
Generated parity atoms are complete for the executable canonical extractor:
the splitter emits one recognized block, no residual CNF, and the GF(2) output
is the generated parity equation.
-/
theorem extractorCompleteOn_clausesForVertex_normal
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ExtractorCompleteness.ExtractorCompleteOn
      (clausesForVertex vars charge)
      [parityClauseForVertex vars charge] := by
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf hnormal with
    ⟨block, hinfer, _hsyntactic, hcompact⟩
  apply ExtractorCompleteness.extractorCompleteOn_of_singleRecognizedGroup
    (key := GroupFrame.canonicalSupportKeyForVars vars)
    (block := block)
  · exact
      GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
        hcnf
  · exact hinfer
  · rw [hcompact]

/--
Two support-disjoint generated parity atoms are complete for the executable
canonical extractor: the grouping pass frames the two generated blocks
independently, the recognizer emits both GF(2) equations, and no residual CNF
remains.
-/
theorem extractorCompleteOn_disjoint_clausesForVertex_append_normal
    {m : Nat}
    {vars1 vars2 : List (Fin m)}
    {charge1 charge2 : Bool}
    {c1 c2 : CNFModel.Clause m}
    {tail1 tail2 : CNFModel.CNF m}
    (hcnf1 : clausesForVertex vars1 charge1 = c1 :: tail1)
    (hcnf2 : clausesForVertex vars2 charge2 = c2 :: tail2)
    (hnormal1 : GroupFrame.VarsInCanonicalSupportOrder vars1)
    (hnormal2 : GroupFrame.VarsInCanonicalSupportOrder vars2)
    (hdisjoint :
      ParityEncoded.DisjointSupport
        (clausesForVertex vars1 charge1)
        (clausesForVertex vars2 charge2))
    (hvars2 : Not (vars2 = [])) :
    ExtractorCompleteness.ExtractorCompleteOn
      (clausesForVertex vars1 charge1 ++
        clausesForVertex vars2 charge2)
      [parityClauseForVertex vars1 charge1,
       parityClauseForVertex vars2 charge2] := by
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf1 hnormal1 with
    ⟨block1, hinfer1, _hsyntactic1, hcompact1⟩
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf2 hnormal2 with
    ⟨block2, hinfer2, _hsyntactic2, hcompact2⟩
  have hgroups1 :
      groupClausesByCanonicalSupport (clausesForVertex vars1 charge1) =
        [(GroupFrame.canonicalSupportKeyForVars vars1,
          clausesForVertex vars1 charge1)] :=
    GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
      hcnf1
  have hgroups2 :
      groupClausesByCanonicalSupport (clausesForVertex vars2 charge2) =
        [(GroupFrame.canonicalSupportKeyForVars vars2,
          clausesForVertex vars2 charge2)] :=
    GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
      hcnf2
  have hnonempty2 :
      GroupFrame.CNFClausesHaveNonemptySupport
        (clausesForVertex vars2 charge2) :=
    GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex
      (m := m) (vars := vars2) (charge := charge2) hvars2
  have hgroupsAppend :
      groupClausesByCanonicalSupport
          (clausesForVertex vars1 charge1 ++
            clausesForVertex vars2 charge2) =
        [(GroupFrame.canonicalSupportKeyForVars vars1,
          clausesForVertex vars1 charge1)] ++
          [(GroupFrame.canonicalSupportKeyForVars vars2,
            clausesForVertex vars2 charge2)] := by
    have hframe :=
      GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
        (clausesForVertex vars1 charge1)
        (clausesForVertex vars2 charge2)
        hdisjoint hnonempty2
    rw [hgroups1, hgroups2] at hframe
    exact hframe
  apply ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition
    (f := clausesForVertex vars1 charge1)
    (g := clausesForVertex vars2 charge2)
    (leftGroups :=
      [(GroupFrame.canonicalSupportKeyForVars vars1,
        clausesForVertex vars1 charge1)])
    (rightGroups :=
      [(GroupFrame.canonicalSupportKeyForVars vars2,
        clausesForVertex vars2 charge2)])
    (leftBlocks := [block1])
    (rightBlocks := [block2])
  · exact hgroupsAppend
  · exact And.intro hinfer1 True.intro
  · exact And.intro hinfer2 True.intro
  · simp [canonicalFingerprintRecognizedBlocksGF2, hcompact1, hcompact2]

/-- Compact GF(2) output for appended canonical block lists is GF(2)-formula append. -/
theorem canonicalFingerprintRecognizedBlocksGF2_append
    {m : Nat}
    (left right : List (CanonicalFingerprintRecognizedParityBlock m)) :
    canonicalFingerprintRecognizedBlocksGF2 (left ++ right) =
      List.append (canonicalFingerprintRecognizedBlocksGF2 left)
        (canonicalFingerprintRecognizedBlocksGF2 right) := by
  simp [canonicalFingerprintRecognizedBlocksGF2]

/--
Induction-step bridge for support-disjoint generated parity atoms.  If a prefix
CNF already has recognized support groups, appending one generated normal-form
parity expansion preserves residual-free extractor completeness and appends the
generated GF(2) equation to the prefix output.
-/
theorem extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized
    {m : Nat}
    {f : CNFModel.CNF m}
    {prefixBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hprefix :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) prefixBlocks)
    (hdisjoint :
      ParityEncoded.DisjointSupport f (clausesForVertex vars charge))
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hvars : Not (vars = [])) :
    ExtractorCompleteness.ExtractorCompleteOn
      (f ++ clausesForVertex vars charge)
      (List.append (canonicalFingerprintRecognizedBlocksGF2 prefixBlocks)
        [parityClauseForVertex vars charge]) := by
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf hnormal with
    ⟨block, hinfer, _hsyntactic, hcompact⟩
  have hgroupsRight :
      groupClausesByCanonicalSupport (clausesForVertex vars charge) =
        [(GroupFrame.canonicalSupportKeyForVars vars,
          clausesForVertex vars charge)] :=
    GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
      hcnf
  have hnonempty :
      GroupFrame.CNFClausesHaveNonemptySupport
        (clausesForVertex vars charge) :=
    GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex
      (m := m) (vars := vars) (charge := charge) hvars
  have hgroupsAppend :
      groupClausesByCanonicalSupport (f ++ clausesForVertex vars charge) =
        groupClausesByCanonicalSupport f ++
          [(GroupFrame.canonicalSupportKeyForVars vars,
            clausesForVertex vars charge)] := by
    have hframe :=
      GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
        f (clausesForVertex vars charge) hdisjoint hnonempty
    rw [hgroupsRight] at hframe
    exact hframe
  apply ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition
    (f := f)
    (g := clausesForVertex vars charge)
    (leftGroups := groupClausesByCanonicalSupport f)
    (rightGroups :=
      [(GroupFrame.canonicalSupportKeyForVars vars,
        clausesForVertex vars charge)])
    (leftBlocks := prefixBlocks)
    (rightBlocks := [block])
  · exact hgroupsAppend
  · exact hprefix
  · exact And.intro hinfer True.intro
  · rw [canonicalFingerprintRecognizedBlocksGF2_append]
    simp [canonicalFingerprintRecognizedBlocksGF2, hcompact]

/--
Induction-step bridge for generated parity atoms whose canonical support key is
fresh for the prefix.  This is weaker than variable-support disjointness: graph
encoders may share edge variables across vertex constraints while still keeping
distinct full incident-support keys.
-/
theorem extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint
    {m : Nat}
    {f : CNFModel.CNF m}
    {prefixBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hprefix :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) prefixBlocks)
    (hkeyDisjoint :
      GroupFrame.CNFClauseKeysDisjoint f (clausesForVertex vars charge))
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ExtractorCompleteness.ExtractorCompleteOn
      (f ++ clausesForVertex vars charge)
      (List.append (canonicalFingerprintRecognizedBlocksGF2 prefixBlocks)
        [parityClauseForVertex vars charge]) := by
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf hnormal with
    ⟨block, hinfer, _hsyntactic, hcompact⟩
  have hgroupsRight :
      groupClausesByCanonicalSupport (clausesForVertex vars charge) =
        [(GroupFrame.canonicalSupportKeyForVars vars,
          clausesForVertex vars charge)] :=
    GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
      hcnf
  have hgroupsAppend :
      groupClausesByCanonicalSupport (f ++ clausesForVertex vars charge) =
        groupClausesByCanonicalSupport f ++
          [(GroupFrame.canonicalSupportKeyForVars vars,
            clausesForVertex vars charge)] := by
    have hframe :=
      GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
        f (clausesForVertex vars charge) hkeyDisjoint
    rw [hgroupsRight] at hframe
    exact hframe
  apply ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition
    (f := f)
    (g := clausesForVertex vars charge)
    (leftGroups := groupClausesByCanonicalSupport f)
    (rightGroups :=
      [(GroupFrame.canonicalSupportKeyForVars vars,
        clausesForVertex vars charge)])
    (leftBlocks := prefixBlocks)
    (rightBlocks := [block])
  · exact hgroupsAppend
  · exact hprefix
  · exact And.intro hinfer True.intro
  · rw [canonicalFingerprintRecognizedBlocksGF2_append]
    simp [canonicalFingerprintRecognizedBlocksGF2, hcompact]

/--
Finite support-disjoint families of generated parity expansions.  The family is
built in snoc order so the executable grouper can use the proved append frame
lemma at every extension step.
-/
inductive GeneratedSupportDisjointFamily (m : Nat) :
    CNFModel.CNF m -> ParityEncoded.GF2Formula m -> Prop
  | empty :
      GeneratedSupportDisjointFamily m [] []
  | snoc
      {f : CNFModel.CNF m}
      {s : ParityEncoded.GF2Formula m}
      {vars : List (Fin m)}
      {charge : Bool}
      {c : CNFModel.Clause m}
      {tail : CNFModel.CNF m}
      (hprefix : GeneratedSupportDisjointFamily m f s)
      (hdisjoint :
        ParityEncoded.DisjointSupport f (clausesForVertex vars charge))
      (hcnf : clausesForVertex vars charge = c :: tail)
      (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
      (hvars : Not (vars = [])) :
      GeneratedSupportDisjointFamily m
        (f ++ clausesForVertex vars charge)
        (List.append s [parityClauseForVertex vars charge])

/--
Every finite support-disjoint generated family has a recognized support-group
decomposition whose compact GF(2) output matches the family target formula up
to permutation.
-/
theorem groupsRecognized_exists_of_generatedSupportDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedSupportDisjointFamily m f s) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) blocks /\
        List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s := by
  induction hfamily with
  | empty =>
      exact Exists.intro [] (And.intro True.intro (List.Perm.refl []))
  | snoc _hprefix hdisjoint hcnf hnormal hvars ih =>
      rename_i fPrefix _sPrefix vars charge _c _tail
      rcases ih with ⟨prefixBlocks, hprefixRecognized, hprefixGF2⟩
      rcases
        inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
          hcnf hnormal with
        ⟨block, hinfer, _hsyntactic, hcompact⟩
      have hgroupsRight :
          groupClausesByCanonicalSupport (clausesForVertex vars charge) =
            [(GroupFrame.canonicalSupportKeyForVars vars,
              clausesForVertex vars charge)] :=
        GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
          hcnf
      have hnonempty :
          GroupFrame.CNFClausesHaveNonemptySupport
            (clausesForVertex vars charge) :=
        GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex
          (m := m) (vars := vars) (charge := charge) hvars
      have hgroupsAppend :
          groupClausesByCanonicalSupport
              (fPrefix ++ clausesForVertex vars charge) =
            groupClausesByCanonicalSupport fPrefix ++
              [(GroupFrame.canonicalSupportKeyForVars vars,
                clausesForVertex vars charge)] := by
        have hframe :=
          GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
            fPrefix (clausesForVertex vars charge) hdisjoint hnonempty
        rw [hgroupsRight] at hframe
        exact hframe
      refine Exists.intro (prefixBlocks ++ [block]) ?_
      constructor
      · rw [hgroupsAppend]
        exact
          ExtractorCompleteness.GroupsRecognized.append
            hprefixRecognized (And.intro hinfer True.intro)
      · rw [canonicalFingerprintRecognizedBlocksGF2_append]
        simp [canonicalFingerprintRecognizedBlocksGF2, hcompact]
        exact hprefixGF2.append_right [parityClauseForVertex vars charge]

/--
Finite support-disjoint generated families are residual-free for the executable
canonical extractor, with the expected accumulated GF(2) formula.
-/
theorem extractorCompleteOn_of_generatedSupportDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedSupportDisjointFamily m f s) :
    ExtractorCompleteness.ExtractorCompleteOn f s := by
  rcases
    groupsRecognized_exists_of_generatedSupportDisjointFamily
      hfamily with
    ⟨blocks, hrecognized, hgf2⟩
  exact
    ExtractorCompleteness.extractorCompleteOn_of_groupRecognition
      (f := f)
      (groups := groupClausesByCanonicalSupport f)
      (blocks := blocks)
      rfl hrecognized hgf2

/--
Finite key-disjoint families of generated parity expansions.  At every snoc
step, the new block's canonical clause-support key must be fresh relative to the
accumulated prefix.  This is the executable extractor condition needed before
moving to ordinary graph/Tseitin encoders with shared edge variables.
-/
inductive GeneratedKeyDisjointFamily (m : Nat) :
    CNFModel.CNF m -> ParityEncoded.GF2Formula m -> Prop
  | empty :
      GeneratedKeyDisjointFamily m [] []
  | snoc
      {f : CNFModel.CNF m}
      {s : ParityEncoded.GF2Formula m}
      {vars : List (Fin m)}
      {charge : Bool}
      {c : CNFModel.Clause m}
      {tail : CNFModel.CNF m}
      (hprefix : GeneratedKeyDisjointFamily m f s)
      (hkeyDisjoint :
        GroupFrame.CNFClauseKeysDisjoint f (clausesForVertex vars charge))
      (hcnf : clausesForVertex vars charge = c :: tail)
      (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
      GeneratedKeyDisjointFamily m
        (f ++ clausesForVertex vars charge)
        (List.append s [parityClauseForVertex vars charge])

/--
Every finite key-disjoint generated family has a recognized support-group
decomposition whose compact GF(2) output matches the family target formula up
to permutation.
-/
theorem groupsRecognized_exists_of_generatedKeyDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedKeyDisjointFamily m f s) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) blocks /\
        List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s := by
  induction hfamily with
  | empty =>
      exact Exists.intro [] (And.intro True.intro (List.Perm.refl []))
  | snoc _hprefix hkeyDisjoint hcnf hnormal ih =>
      rename_i fPrefix _sPrefix vars charge _c _tail
      rcases ih with ⟨prefixBlocks, hprefixRecognized, hprefixGF2⟩
      rcases
        inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
          hcnf hnormal with
        ⟨block, hinfer, _hsyntactic, hcompact⟩
      have hgroupsRight :
          groupClausesByCanonicalSupport (clausesForVertex vars charge) =
            [(GroupFrame.canonicalSupportKeyForVars vars,
              clausesForVertex vars charge)] :=
        GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
          hcnf
      have hgroupsAppend :
          groupClausesByCanonicalSupport
              (fPrefix ++ clausesForVertex vars charge) =
            groupClausesByCanonicalSupport fPrefix ++
              [(GroupFrame.canonicalSupportKeyForVars vars,
                clausesForVertex vars charge)] := by
        have hframe :=
          GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
            fPrefix (clausesForVertex vars charge) hkeyDisjoint
        rw [hgroupsRight] at hframe
        exact hframe
      refine Exists.intro (prefixBlocks ++ [block]) ?_
      constructor
      · rw [hgroupsAppend]
        exact
          ExtractorCompleteness.GroupsRecognized.append
            hprefixRecognized (And.intro hinfer True.intro)
      · rw [canonicalFingerprintRecognizedBlocksGF2_append]
        simp [canonicalFingerprintRecognizedBlocksGF2, hcompact]
        exact hprefixGF2.append_right [parityClauseForVertex vars charge]

/--
Finite key-disjoint generated families are residual-free for the executable
canonical extractor, with the expected accumulated GF(2) formula.
-/
theorem extractorCompleteOn_of_generatedKeyDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedKeyDisjointFamily m f s) :
    ExtractorCompleteness.ExtractorCompleteOn f s := by
  rcases
    groupsRecognized_exists_of_generatedKeyDisjointFamily
      hfamily with
    ⟨blocks, hrecognized, hgf2⟩
  exact
    ExtractorCompleteness.extractorCompleteOn_of_groupRecognition
      (f := f)
      (groups := groupClausesByCanonicalSupport f)
      (blocks := blocks)
      rfl hrecognized hgf2

/--
Generated key-disjoint families also produce declarative parity-encoded class
witnesses. The key-disjoint hypothesis is stronger than semantic class
membership needs; it is retained by the family certificate for the executable
extractor lane.
-/
theorem class_of_generatedKeyDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedKeyDisjointFamily m f s) :
    ParityEncoded.Class m f s := by
  induction hfamily with
  | empty =>
      exact ParityEncoded.Class.empty
  | snoc _hprefix _hkeyDisjoint _hcnf _hnormal ih =>
      rename_i _fPrefix _sPrefix vars charge _c _tail
      have hatom :
          ParityEncoded.Class m
            (clausesForVertex vars charge)
            [parityClauseForVertex vars charge] :=
        ParityEncoded.Class.atom vars charge
          (clausesForVertex vars charge) (List.Perm.refl _)
      exact ParityEncoded.Class.append ih hatom

/--
Generated key-disjoint families satisfy the combined semantic/executable
extraction claim: they are semantically equivalent to their folded GF(2)
formula and residual-free for the executable canonical splitter.
-/
theorem semanticExtractorCompleteOn_of_generatedKeyDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedKeyDisjointFamily m f s) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f s :=
  ExtractorCompleteness.semanticExtractorCompleteOn_of_class
    (class_of_generatedKeyDisjointFamily hfamily)
    (extractorCompleteOn_of_generatedKeyDisjointFamily hfamily)

/-- A generated parity specification is a variable list plus its parity charge. -/
abbrev GeneratedParitySpec (m : Nat) := List (Fin m) × Bool

/-- Ordinary CNF expansion for one generated parity specification. -/
def generatedParitySpecCNF {m : Nat} (spec : GeneratedParitySpec m) :
    CNFModel.CNF m :=
  clausesForVertex spec.1 spec.2

/-- Compact GF(2) equation for one generated parity specification. -/
def generatedParitySpecGF2 {m : Nat} (spec : GeneratedParitySpec m) :
    ResoplusPDT.ParityClause (Basic.CNF.mk m) :=
  parityClauseForVertex spec.1 spec.2

/-- Ordinary CNF expansion for a finite list of generated parity specs. -/
def generatedParitySpecsCNF {m : Nat} (specs : List (GeneratedParitySpec m)) :
    CNFModel.CNF m :=
  specs.foldl (fun acc spec => acc ++ generatedParitySpecCNF spec) []

/-- Compact GF(2) formula for a finite list of generated parity specs. -/
def generatedParitySpecsGF2 {m : Nat} (specs : List (GeneratedParitySpec m)) :
    ParityEncoded.GF2Formula m :=
  specs.foldl
    (fun acc spec => List.append acc [generatedParitySpecGF2 spec]) []

/-- Folding generated CNF specs over a snoc appends the last generated block. -/
theorem generatedParitySpecsCNF_append_singleton
    {m : Nat}
    (specs : List (GeneratedParitySpec m))
    (spec : GeneratedParitySpec m) :
    generatedParitySpecsCNF (specs ++ [spec]) =
      generatedParitySpecsCNF specs ++ generatedParitySpecCNF spec := by
  simp [generatedParitySpecsCNF, generatedParitySpecCNF, List.foldl_append]

/-- Folding generated GF(2) specs over a snoc appends the last generated equation. -/
theorem generatedParitySpecsGF2_append_singleton
    {m : Nat}
    (specs : List (GeneratedParitySpec m))
    (spec : GeneratedParitySpec m) :
    generatedParitySpecsGF2 (specs ++ [spec]) =
      List.append (generatedParitySpecsGF2 specs) [generatedParitySpecGF2 spec] := by
  simp [generatedParitySpecsGF2, generatedParitySpecGF2, List.foldl_append]

/-- Folding by appending singleton outputs is extensionally the same as mapping. -/
theorem foldl_append_singleton_eq_append_map
    {alpha beta : Type} (f : alpha -> beta) :
    forall (xs : List alpha) (acc : List beta),
      xs.foldl (fun acc x => acc ++ [f x]) acc = acc ++ xs.map f := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp
  | cons x xs ih =>
      intro acc
      simp [List.foldl]
      rw [ih (acc ++ [f x])]
      simp [List.append_assoc]

/-- Folding by appending list outputs is extensionally the same as bind. -/
theorem foldl_append_eq_append_bind
    {alpha beta : Type} (f : alpha -> List beta) :
    forall (xs : List alpha) (acc : List beta),
      xs.foldl (fun acc x => acc ++ f x) acc = acc ++ xs.bind f := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp
  | cons x xs ih =>
      intro acc
      simp [List.foldl]
      rw [ih (acc ++ f x)]
      simp [List.append_assoc]

/-- The generated-spec CNF fold is the bind of each spec's expanded CNF. -/
theorem generatedParitySpecsCNF_eq_bind
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    generatedParitySpecsCNF specs =
      specs.bind generatedParitySpecCNF := by
  simp [generatedParitySpecsCNF, foldl_append_eq_append_bind]

/-- The generated-spec GF(2) fold is the map of each spec's compact equation. -/
theorem generatedParitySpecsGF2_eq_map
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    generatedParitySpecsGF2 specs =
      specs.map generatedParitySpecGF2 := by
  simp [generatedParitySpecsGF2, foldl_append_singleton_eq_append_map]

/-- All generated parity specifications in a list use the same support vars. -/
def GeneratedParitySpecsSameSupportVars {m : Nat}
    (specs : List (GeneratedParitySpec m)) (vars : List (Fin m)) : Prop :=
  forall spec : GeneratedParitySpec m, List.Mem spec specs -> spec.1 = vars

/-- Generate a same-support parity-spec list from one support and a charge list. -/
def generatedParitySpecsForSupportCharges {m : Nat}
    (vars : List (Fin m)) (charges : List Bool) :
    List (GeneratedParitySpec m) :=
  charges.map (fun charge => (vars, charge))

/-- Specs generated from one support and a charge list are same-support specs. -/
theorem generatedParitySpecsForSupportCharges_sameSupport
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    GeneratedParitySpecsSameSupportVars
      (generatedParitySpecsForSupportCharges vars charges) vars := by
  intro spec hspec
  unfold generatedParitySpecsForSupportCharges at hspec
  rcases List.mem_map.1 hspec with ⟨charge, _hcharge, hspec_eq⟩
  cases hspec_eq
  rfl

/-- The same-support generated CNF fold exposes its head block by append. -/
theorem generatedParitySpecsCNF_forSupportCharges_cons
    {m : Nat} (vars : List (Fin m)) (charge : Bool)
    (charges : List Bool) :
    generatedParitySpecsCNF
        (generatedParitySpecsForSupportCharges vars (charge :: charges)) =
      clausesForVertex vars charge ++
        generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges) := by
  rw [generatedParitySpecsCNF_eq_bind, generatedParitySpecsCNF_eq_bind]
  simp [generatedParitySpecsForSupportCharges, generatedParitySpecCNF]

/--
On the merged same-support generated CNF, the all-false clause fingerprint is
present exactly when at least one hidden generated charge is true. This is a
pre-split CNF-side presence signal; it does not claim multiplicity recovery.
-/
theorem allFalseClauseFingerprint_mem_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_iff_true_mem
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    List.Mem
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false)))
      (canonicalBlockFingerprint
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) <->
      List.Mem true charges := by
  induction charges with
  | nil =>
      constructor
      · intro hmem
        rcases mem_canonicalBlockFingerprint_iff.1 hmem with ⟨c, hc, _hfp⟩
        simp [generatedParitySpecsForSupportCharges, generatedParitySpecsCNF] at hc
        cases hc
      · intro hmem
        cases hmem
  | cons charge charges ih =>
      rw [generatedParitySpecsCNF_forSupportCharges_cons]
      rw [mem_canonicalBlockFingerprint_append_iff]
      cases charge
      · have hfalse :=
          allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false
            vars
        constructor
        · intro hmem
          rcases hmem with hblock | htail
          · exact False.elim (hfalse hblock)
          · exact List.Mem.tail false (ih.1 htail)
        · intro hmem
          cases hmem with
          | tail _ htail =>
              exact Or.inr (ih.2 htail)
      · have htrue :=
          allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true
            vars
        constructor
        · intro _hmem
          exact List.Mem.head charges
        · intro _hmem
          exact Or.inl htrue

/--
The same merged-CNF all-false fingerprint presence signal is invariant under
clause permutation of the generated same-support component.
-/
theorem allFalseClauseFingerprint_mem_targetFingerprint_iff_true_mem_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    List.Mem
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false)))
      (canonicalBlockFingerprint target) <->
      List.Mem true charges := by
  have hfingerprint :
      canonicalBlockFingerprint target =
        canonicalBlockFingerprint
          (generatedParitySpecsCNF
            (generatedParitySpecsForSupportCharges vars charges)) :=
    canonicalBlockFingerprint_eq_of_perm hperm
  rw [hfingerprint]
  exact
    allFalseClauseFingerprint_mem_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_iff_true_mem
      vars charges

/--
On a merged same-support generated CNF, the all-false clause-fingerprint count
lower-bounds the true-charge multiplicity.  The exact count theorem below
strengthens this compatibility lemma.
-/
theorem allFalseClauseFingerprint_count_true_le_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    charges.count true <=
      (canonicalBlockFingerprint
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))).count
        (canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false))) := by
  induction charges with
  | nil =>
      exact Nat.zero_le _
  | cons charge charges ih =>
      rw [generatedParitySpecsCNF_forSupportCharges_cons]
      rw [canonicalBlockFingerprint_count_append]
      cases charge
      · have hfalse :=
          allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_false
            vars
        simpa [hfalse] using ih
      · have htrue :=
          one_le_allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true
            vars
        simp
        omega

/--
On a merged same-support generated CNF, the all-false clause-fingerprint count
is exactly the true-charge multiplicity.  This is the direct merged-component
counterpart of the single-block exact count theorem.
-/
theorem allFalseClauseFingerprint_count_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_eq_true_count
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    (canonicalBlockFingerprint
      (generatedParitySpecsCNF
        (generatedParitySpecsForSupportCharges vars charges))).count
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false))) =
      charges.count true := by
  induction charges with
  | nil =>
      unfold canonicalBlockFingerprint
      rw [sortClauseFingerprints_count_eq]
      simp [generatedParitySpecsForSupportCharges, generatedParitySpecsCNF]
  | cons charge charges ih =>
      rw [generatedParitySpecsCNF_forSupportCharges_cons]
      rw [canonicalBlockFingerprint_count_append]
      cases charge
      case false =>
        have hfalse :=
          allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_false
            vars
        simpa [hfalse] using ih
      case true =>
        have htrue :=
          allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true_eq_one
            vars
        simp [htrue, ih, Nat.add_comm]

/--
The merged-CNF all-false fingerprint count lower bound is invariant under
clause permutation of the generated same-support component.
-/
theorem allFalseClauseFingerprint_count_true_le_targetFingerprint_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    charges.count true <=
      (canonicalBlockFingerprint target).count
        (canonicalClauseFingerprint
          (clauseForAssignment vars (List.replicate vars.length false))) := by
  have hfingerprint :
      canonicalBlockFingerprint target =
        canonicalBlockFingerprint
          (generatedParitySpecsCNF
            (generatedParitySpecsForSupportCharges vars charges)) :=
    canonicalBlockFingerprint_eq_of_perm hperm
  rw [hfingerprint]
  exact
    allFalseClauseFingerprint_count_true_le_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges
      vars charges

/--
The exact merged-CNF all-false fingerprint count is invariant under clause
permutation of the generated same-support component.
-/
theorem allFalseClauseFingerprint_count_targetFingerprint_eq_true_count_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    (canonicalBlockFingerprint target).count
      (canonicalClauseFingerprint
        (clauseForAssignment vars (List.replicate vars.length false))) =
      charges.count true := by
  have hfingerprint :
      canonicalBlockFingerprint target =
        canonicalBlockFingerprint
          (generatedParitySpecsCNF
            (generatedParitySpecsForSupportCharges vars charges)) :=
    canonicalBlockFingerprint_eq_of_perm hperm
  rw [hfingerprint]
  exact
    allFalseClauseFingerprint_count_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_eq_true_count
      vars charges

/-- Canonical charge-list representative from total and true-charge counts. -/
def canonicalSupportChargesFromCounts (totalCharges trueCharges : Nat) : List Bool :=
  List.replicate (totalCharges - trueCharges) false ++
    List.replicate trueCharges true

/-- The canonical charge-list representative has the requested true count. -/
theorem canonicalSupportChargesFromCounts_count_true
    (totalCharges trueCharges : Nat) :
    (canonicalSupportChargesFromCounts totalCharges trueCharges).count true =
      trueCharges := by
  simp [canonicalSupportChargesFromCounts, List.count_append,
    List.count_replicate]

/-- The canonical charge-list representative has the requested false count. -/
theorem canonicalSupportChargesFromCounts_count_false
    (totalCharges trueCharges : Nat) :
    (canonicalSupportChargesFromCounts totalCharges trueCharges).count false =
      totalCharges - trueCharges := by
  simp [canonicalSupportChargesFromCounts, List.count_append,
    List.count_replicate]

/-- In a Boolean list, false-count is length minus true-count. -/
theorem bool_count_false_eq_length_sub_count_true (charges : List Bool) :
    charges.count false = charges.length - charges.count true := by
  induction charges with
  | nil => simp
  | cons charge charges ih =>
      have hle : charges.count true <= charges.length :=
        List.count_le_length true charges
      cases charge
      case false =>
        simp [List.count_cons, ih]
        omega
      case true =>
        simp [List.count_cons, ih]

/--
The canonical representative built from a Boolean charge list's length and
true-count is permutation-equivalent to the original charge list.
-/
theorem canonicalSupportChargesFromCounts_perm (charges : List Bool) :
    List.Perm
      (canonicalSupportChargesFromCounts charges.length (charges.count true))
      charges := by
  rw [List.perm_iff_count]
  intro charge
  cases charge
  case false =>
    rw [canonicalSupportChargesFromCounts_count_false]
    exact (bool_count_false_eq_length_sub_count_true charges).symm
  case true =>
    exact canonicalSupportChargesFromCounts_count_true
      charges.length (charges.count true)

/-- Same-support generated CNFs are invariant under charge-list permutation. -/
theorem generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm
    {m : Nat} (vars : List (Fin m)) {charges1 charges2 : List Bool}
    (hperm : List.Perm charges1 charges2) :
    List.Perm
      (generatedParitySpecsCNF
        (generatedParitySpecsForSupportCharges vars charges1))
      (generatedParitySpecsCNF
        (generatedParitySpecsForSupportCharges vars charges2)) := by
  rw [generatedParitySpecsCNF_eq_bind, generatedParitySpecsCNF_eq_bind]
  exact List.Perm.bind_right generatedParitySpecCNF
    (List.Perm.map (fun charge => (vars, charge)) hperm)

/--
If every generated block over the support has the same ordinary CNF length,
then the generated same-support component length is exactly charge-count times
that block length.  This is the syntactic multiplicity counterpart to the
charge-presence semantic lemmas below.
-/
theorem generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) (k : Nat)
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k) :
    (generatedParitySpecsCNF
      (generatedParitySpecsForSupportCharges vars charges)).length =
        charges.length * k := by
  rw [generatedParitySpecsCNF_eq_bind]
  induction charges with
  | nil =>
      simp [generatedParitySpecsForSupportCharges]
  | cons charge charges ih =>
      have hhead :
          (clausesForVertex vars charge).length = k :=
        hlen charge (List.Mem.head charges)
      have htail :
          forall charge' : Bool, List.Mem charge' charges ->
            (clausesForVertex vars charge').length = k := by
        intro charge' hmem
        exact hlen charge' (List.Mem.tail charge hmem)
      have ih' := ih htail
      calc
        ((generatedParitySpecsForSupportCharges vars (charge :: charges)).bind
            generatedParitySpecCNF).length =
            k + ((generatedParitySpecsForSupportCharges vars charges).bind
              generatedParitySpecCNF).length := by
          simp [generatedParitySpecsForSupportCharges, generatedParitySpecCNF,
            hhead]
        _ = k + charges.length * k := by
          rw [ih']
        _ = (charge :: charges).length * k := by
          simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]

/--
For a clause permutation of a same-support generated component whose generated
blocks all have length `k`, the target component length exactly determines the
total generated charge count times `k`.
-/
theorem target_length_eq_charge_count_mul_block_length_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    {k : Nat}
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    target.length = charges.length * k := by
  exact hperm.length_eq.trans
    (generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length
      vars charges k hlen)

/--
For a positive generated block length `k`, the target length quotient by `k`
is exactly the hidden generated charge-list length.
-/
theorem charges_length_eq_target_length_div_block_length_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    {k : Nat}
    (hk : 0 < k)
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    charges.length = target.length / k := by
  have htarget :=
    target_length_eq_charge_count_mul_block_length_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  calc
    charges.length = (charges.length * k) / k := by
      exact (Nat.mul_div_left charges.length hk).symm
    _ = target.length / k := by
      simp [htarget]

/-- Generated same-support component lengths are divisible by their block size. -/
theorem target_length_mod_block_length_eq_zero_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    {k : Nat}
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    target.length % k = 0 := by
  have htarget :=
    target_length_eq_charge_count_mul_block_length_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  rw [htarget]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left k charges.length)

/-- Exact same-support generated CNF length for arity-three parity blocks. -/
theorem generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_three
    {m : Nat} {vars : List (Fin m)}
    (charges : List Bool)
    (hlen : vars.length = 3) :
    (generatedParitySpecsCNF
      (generatedParitySpecsForSupportCharges vars charges)).length =
        charges.length * 4 := by
  exact
    generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length
      vars charges 4
      (by
        intro charge _hmem
        exact clausesForVertex_length_of_length_three (vars := vars)
          (charge := charge) hlen)

/-- Exact same-support generated CNF length for arity-four parity blocks. -/
theorem generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_four
    {m : Nat} {vars : List (Fin m)}
    (charges : List Bool)
    (hlen : vars.length = 4) :
    (generatedParitySpecsCNF
      (generatedParitySpecsForSupportCharges vars charges)).length =
        charges.length * 8 := by
  exact
    generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length
      vars charges 8
      (by
        intro charge _hmem
        exact clausesForVertex_length_of_length_four (vars := vars)
          (charge := charge) hlen)

/--
For a clause permutation of an arity-three same-support generated component,
the component length exactly determines the total generated charge count.
-/
theorem target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    target.length = charges.length * 4 := by
  exact hperm.length_eq.trans
    (generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_three
      (vars := vars) charges hlen)

/--
For a clause permutation of an arity-four same-support generated component,
the component length exactly determines the total generated charge count.
-/
theorem target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    target.length = charges.length * 8 := by
  exact hperm.length_eq.trans
    (generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_four
      (vars := vars) charges hlen)

/--
For arity-three same-support generated components, the component length quotient
by four is exactly the generated charge-list length.
-/
theorem charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    charges.length = target.length / 4 := by
  have htarget :=
    target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  calc
    charges.length = (charges.length * 4) / 4 := by
      exact (Nat.mul_div_left charges.length (by decide : 0 < 4)).symm
    _ = target.length / 4 := by
      simp [htarget]

/--
Arity-three same-support generated component lengths are divisible by four.
-/
theorem target_length_mod_four_eq_zero_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    target.length % 4 = 0 := by
  have htarget :=
    target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  rw [htarget]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 4 charges.length)

/--
For arity-four same-support generated components, the component length quotient
by eight is exactly the generated charge-list length.
-/
theorem charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    charges.length = target.length / 8 := by
  have htarget :=
    target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  calc
    charges.length = (charges.length * 8) / 8 := by
      exact (Nat.mul_div_left charges.length (by decide : 0 < 8)).symm
    _ = target.length / 8 := by
      simp [htarget]

/--
Arity-four same-support generated component lengths are divisible by eight.
-/
theorem target_length_mod_eight_eq_zero_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    target.length % 8 = 0 := by
  have htarget :=
    target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  rw [htarget]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 8 charges.length)

/-- The all-false clause-fingerprint multiplicity in a target component. -/
def allFalseFingerprintCount {m : Nat}
    (vars : List (Fin m)) (target : CNFModel.CNF m) : Nat :=
  (canonicalBlockFingerprint target).count
    (canonicalClauseFingerprint
      (clauseForAssignment vars (List.replicate vars.length false)))

/--
Direct charge-list reconstruction from target length and all-false fingerprint
count, parameterized by the ordinary CNF block size for one parity equation.
-/
def directSameSupportChargesFromTargetWithBlockSize {m : Nat}
    (vars : List (Fin m)) (target : CNFModel.CNF m) (blockSize : Nat) :
    List Bool :=
  canonicalSupportChargesFromCounts
    (target.length / blockSize)
    (allFalseFingerprintCount vars target)

/--
The generated one-block CNF size inferred from support arity.  Empty support is
mapped to zero so executable direct-recovery callers keep rejecting that edge
case through the existing positive-block-size guard.
-/
def generatedParitySupportBlockSize {m : Nat} (vars : List (Fin m)) : Nat :=
  if vars = [] then 0 else 2 ^ (vars.length - 1)

/-- Nonempty generated support has the expected inferred block size. -/
theorem generatedParitySupportBlockSize_eq_pow_pred_of_vars_ne_empty
    {m : Nat} {vars : List (Fin m)}
    (hvars : Not (vars = [])) :
    generatedParitySupportBlockSize vars = 2 ^ (vars.length - 1) := by
  simp [generatedParitySupportBlockSize, hvars]

/-- The inferred generated block size is positive for every nonempty support. -/
theorem generatedParitySupportBlockSize_pos_of_vars_ne_empty
    {m : Nat} {vars : List (Fin m)}
    (hvars : Not (vars = [])) :
    0 < generatedParitySupportBlockSize vars := by
  rw [generatedParitySupportBlockSize_eq_pow_pred_of_vars_ne_empty hvars]
  exact Nat.pow_pos (by decide : 0 < 2)

/--
For nonempty generated support, the inferred block-size function matches the
actual generated CNF size of either charge.
-/
theorem clausesForVertex_length_eq_generatedParitySupportBlockSize
    {m : Nat} {vars : List (Fin m)} {charge : Bool}
    (hvars : Not (vars = [])) :
    (clausesForVertex vars charge).length =
      generatedParitySupportBlockSize vars := by
  rw [generatedParitySupportBlockSize_eq_pow_pred_of_vars_ne_empty hvars]
  exact clausesForVertex_length_eq_pow_pred_of_vars_ne_empty hvars

/--
For any positive certified block size `k`, the direct count-derived charge list
is permutation-equivalent to the hidden charge list.  The arity-specific
theorems below are instances of this block-size-generic statement.
-/
theorem directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_of_block_length
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    {k : Nat}
    (hk : 0 < k)
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    List.Perm
      (directSameSupportChargesFromTargetWithBlockSize vars target k)
      charges := by
  unfold directSameSupportChargesFromTargetWithBlockSize
  unfold allFalseFingerprintCount
  have hlenCharges :=
    charges_length_eq_target_length_div_block_length_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hk hlen hperm
  have htrueCount :=
    allFalseClauseFingerprint_count_targetFingerprint_eq_true_count_of_perm_supportCharges
      (vars := vars) (charges := charges) (target := target) hperm
  rw [hlenCharges.symm, htrueCount]
  exact canonicalSupportChargesFromCounts_perm charges

/--
For arity-three generated same-support components, the direct count-derived
charge list is permutation-equivalent to the hidden charge list.
-/
theorem directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityThree
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    List.Perm
      (directSameSupportChargesFromTargetWithBlockSize vars target 4)
      charges := by
  unfold directSameSupportChargesFromTargetWithBlockSize
  unfold allFalseFingerprintCount
  have hlenCharges :=
    charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  have htrueCount :=
    allFalseClauseFingerprint_count_targetFingerprint_eq_true_count_of_perm_supportCharges
      (vars := vars) (charges := charges) (target := target) hperm
  rw [hlenCharges.symm, htrueCount]
  exact canonicalSupportChargesFromCounts_perm charges

/--
For arity-four generated same-support components, the direct count-derived
charge list is permutation-equivalent to the hidden charge list.
-/
theorem directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityFour
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    List.Perm
      (directSameSupportChargesFromTargetWithBlockSize vars target 8)
      charges := by
  unfold directSameSupportChargesFromTargetWithBlockSize
  unfold allFalseFingerprintCount
  have hlenCharges :=
    charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges
      (vars := vars) (charges := charges) (target := target) hlen hperm
  have htrueCount :=
    allFalseClauseFingerprint_count_targetFingerprint_eq_true_count_of_perm_supportCharges
      (vars := vars) (charges := charges) (target := target) hperm
  rw [hlenCharges.symm, htrueCount]
  exact canonicalSupportChargesFromCounts_perm charges

/--
For any nonempty generated support, the support-size-derived direct charge list
is permutation-equivalent to the hidden charge list.
-/
theorem directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_supportSize
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : Not (vars = []))
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    List.Perm
      (directSameSupportChargesFromTargetWithBlockSize vars target
        (generatedParitySupportBlockSize vars))
      charges := by
  exact
    directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_of_block_length
      (vars := vars) (charges := charges) (target := target)
      (generatedParitySupportBlockSize_pos_of_vars_ne_empty hvars)
      (by
        intro charge _hmem
        exact clausesForVertex_length_eq_generatedParitySupportBlockSize
          (vars := vars) (charge := charge) hvars)
      hperm

/-- The compact GF(2) formula for same-support charges is just the charge map. -/
theorem generatedParitySpecsGF2_forSupportCharges_eq_map
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    generatedParitySpecsGF2
        (generatedParitySpecsForSupportCharges vars charges) =
      charges.map (fun charge => parityClauseForVertex vars charge) := by
  rw [generatedParitySpecsGF2_eq_map]
  simp [generatedParitySpecsForSupportCharges, generatedParitySpecGF2]

/--
The compact GF(2) RHS projection for generated same-support charges is exactly
the input charge list.  Thus the compact generated core preserves charge
multiplicity even though its satisfaction semantics only observes charge
presence.
-/
theorem generatedParitySpecsGF2_forSupportCharges_rhs_eq
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsGF2
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun c => c.rhs)) = charges := by
  rw [generatedParitySpecsGF2_forSupportCharges_eq_map]
  simp only [List.map_map]
  change List.map (fun charge => charge) charges = charges
  exact List.map_id' charges

/-- True-charge multiplicity is preserved in the compact generated GF(2) core. -/
theorem generatedParitySpecsGF2_forSupportCharges_rhs_count_true
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsGF2
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun c => c.rhs)).count true = charges.count true := by
  rw [generatedParitySpecsGF2_forSupportCharges_rhs_eq]

/-- False-charge multiplicity is preserved in the compact generated GF(2) core. -/
theorem generatedParitySpecsGF2_forSupportCharges_rhs_count_false
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsGF2
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun c => c.rhs)).count false = charges.count false := by
  rw [generatedParitySpecsGF2_forSupportCharges_rhs_eq]

/--
Same-support generated GF(2) semantics depends only on which charges appear in
the charge list.  Multiplicity is therefore a syntactic coverage issue, not a
semantic one.
-/
theorem gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem
    {m : Nat} (a : CNFModel.Assignment m)
    (vars : List (Fin m)) (charges : List Bool) :
    ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a
        (generatedParitySpecsGF2
          (generatedParitySpecsForSupportCharges vars charges)) <->
      forall charge : Bool, List.Mem charge charges ->
        ResoplusPDT.ClauseSat
          (F := Basic.CNF.mk m) a
          (parityClauseForVertex vars charge) := by
  rw [generatedParitySpecsGF2_forSupportCharges_eq_map]
  constructor
  · intro hsat charge hmem
    exact hsat (parityClauseForVertex vars charge)
      (List.mem_map.2 ⟨charge, hmem, rfl⟩)
  · intro hsat c hc
    rcases List.mem_map.1 hc with ⟨charge, hmem, hc_eq⟩
    cases hc_eq
    exact hsat charge hmem

/-- Duplicate same-support charges do not change the generated GF(2) semantics. -/
theorem gf2Sat_generatedParitySpecsForSupportCharges_iff_eraseDups
    {m : Nat} (a : CNFModel.Assignment m)
    (vars : List (Fin m)) (charges : List Bool) :
    ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a
        (generatedParitySpecsGF2
          (generatedParitySpecsForSupportCharges vars charges)) <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a
        (generatedParitySpecsGF2
          (generatedParitySpecsForSupportCharges vars charges.eraseDups)) := by
  rw [gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem,
    gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem]
  constructor
  · intro hsat charge hmem
    exact hsat charge ((GroupFrame.mem_eraseDups_iff charge charges).1 hmem)
  · intro hsat charge hmem
    exact hsat charge ((GroupFrame.mem_eraseDups_iff charge charges).2 hmem)

/--
Since the only possible charges are `false` and `true`, same-support generated
GF(2) semantics is exactly the pair of charge-presence obligations.
-/
theorem gf2Sat_generatedParitySpecsForSupportCharges_iff_charge_presence
    {m : Nat} (a : CNFModel.Assignment m)
    (vars : List (Fin m)) (charges : List Bool) :
    ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a
        (generatedParitySpecsGF2
          (generatedParitySpecsForSupportCharges vars charges)) <->
      ((List.Mem false charges ->
          ResoplusPDT.ClauseSat
            (F := Basic.CNF.mk m) a
            (parityClauseForVertex vars false)) /\
        (List.Mem true charges ->
          ResoplusPDT.ClauseSat
            (F := Basic.CNF.mk m) a
            (parityClauseForVertex vars true))) := by
  rw [gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem]
  constructor
  · intro hsat
    exact ⟨hsat false, hsat true⟩
  · intro hsat charge hmem
    cases charge
    · exact hsat.1 hmem
    · exact hsat.2 hmem

/--
A same-support generated GF(2) formula containing both charges is unsatisfiable.
This is the semantic boundary behind mixed-charge same-support components.
-/
theorem not_gf2Sat_generatedParitySpecsForSupportCharges_of_mem_false_true
    {m : Nat} (a : CNFModel.Assignment m)
    (vars : List (Fin m)) {charges : List Bool}
    (hfalse : List.Mem false charges)
    (htrue : List.Mem true charges) :
    Not
      (ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a
        (generatedParitySpecsGF2
          (generatedParitySpecsForSupportCharges vars charges))) := by
  intro hsat
  have hpresence :=
    (gf2Sat_generatedParitySpecsForSupportCharges_iff_charge_presence
      a vars charges).1 hsat
  have hsatFalse :
      ResoplusPDT.ClauseSat
        (F := Basic.CNF.mk m) a
        (parityClauseForVertex vars false) :=
    hpresence.1 hfalse
  have hsatTrue :
      ResoplusPDT.ClauseSat
        (F := Basic.CNF.mk m) a
        (parityClauseForVertex vars true) :=
    hpresence.2 htrue
  have hparFalse :
      (parity (assignmentRow a vars) == false) = true :=
    (clauseSat_parityClauseForVertex_iff_parity_eq
      (m := m) a (vars := vars) (charge := false)).1 hsatFalse
  have hparTrue :
      (parity (assignmentRow a vars) == true) = true :=
    (clauseSat_parityClauseForVertex_iff_parity_eq
      (m := m) a (vars := vars) (charge := true)).1 hsatTrue
  cases hpar : parity (assignmentRow a vars) <;> simp [hpar] at hparFalse hparTrue

/-- Return the first successful optional result from a finite candidate list. -/
def firstSome? {alpha beta : Type} : List alpha -> (alpha -> Option beta) -> Option beta
  | [], _ => none
  | x :: xs, f =>
      match f x with
      | some y => some y
      | none => firstSome? xs f

/-- A successful `firstSome?` result comes from one of the searched candidates. -/
theorem firstSome?_eq_some_imp_exists_mem
    {alpha beta : Type} {xs : List alpha} {f : alpha -> Option beta} {y : beta}
    (h : firstSome? xs f = some y) :
    exists x : alpha, List.Mem x xs /\ f x = some y := by
  induction xs with
  | nil =>
      simp [firstSome?] at h
  | cons x xs ih =>
      unfold firstSome? at h
      cases hx : f x with
      | none =>
          have htail : firstSome? xs f = some y := by
            simpa [hx] using h
          rcases ih htail with ⟨x', hxmem, hfx⟩
          exact ⟨x', List.Mem.tail x hxmem, hfx⟩
      | some y' =>
          have hy : y' = y := by
            simpa [hx] using h
          exact ⟨x, List.Mem.head xs, by simpa [hy] using hx⟩

/-- If a searched candidate succeeds, then `firstSome?` returns some result. -/
theorem firstSome?_exists_some_of_mem_eq_some
    {alpha beta : Type} {xs : List alpha} {f : alpha -> Option beta}
    {x : alpha} {y : beta}
    (hmem : List.Mem x xs) (hfx : f x = some y) :
    exists y' : beta, firstSome? xs f = some y' := by
  induction xs with
  | nil =>
      cases hmem
  | cons z zs ih =>
      unfold firstSome?
      cases hz : f z with
      | none =>
          cases hmem with
          | head =>
              rw [hfx] at hz
              cases hz
          | tail _ htail =>
              exact ih htail
      | some zval =>
          exact ⟨zval, rfl⟩

/-- All Boolean charge lists up to a supplied length bound. -/
def chargeListsUpTo (maxCharges : Nat) : List (List Bool) :=
  (List.range (maxCharges + 1)).bind allAssignments

/-- Every Boolean charge list within the bound is in `chargeListsUpTo`. -/
theorem mem_chargeListsUpTo_of_length_le
    {charges : List Bool} {maxCharges : Nat}
    (hle : charges.length <= maxCharges) :
    List.Mem charges (chargeListsUpTo maxCharges) := by
  unfold chargeListsUpTo
  exact List.mem_bind.2
    ⟨charges.length,
      List.mem_range.2 (Nat.lt_succ_of_le hle),
      mem_allAssignments_of_length rfl⟩

/--
Two generated parity expansions over the same canonical support have
support-variable-homogeneous ordinary clauses.
-/
theorem cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_two_sameSupport
    {m : Nat}
    (vars : List (Fin m))
    (charge1 charge2 : Bool)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    GroupFrame.CNFClausesHaveCanonicalSupportVars
      (generatedParitySpecsCNF [(vars, charge1), (vars, charge2)])
      vars := by
  intro c hc
  rw [generatedParitySpecsCNF_eq_bind] at hc
  have hcappend :
      List.Mem c
        (generatedParitySpecCNF (vars, charge1) ++
          generatedParitySpecCNF (vars, charge2)) := by
    simpa [List.bind] using hc
  rcases List.mem_append.1 hcappend with hleft | hright
  ·
      have hleft' : List.Mem c (clausesForVertex vars charge1) := by
        simpa [generatedParitySpecCNF] using hleft
      exact
        (GroupFrame.cnfClausesHaveCanonicalSupportVars_clausesForVertex
          (m := m) vars charge1 c hleft').trans hnormal
  ·
      have hright' : List.Mem c (clausesForVertex vars charge2) := by
        simpa [generatedParitySpecCNF] using hright
      exact
        (GroupFrame.cnfClausesHaveCanonicalSupportVars_clausesForVertex
          (m := m) vars charge2 c hright').trans hnormal

/--
Any generated parity-spec list whose specs all use the same canonical support
has support-variable-homogeneous ordinary clauses, regardless of length or
charge pattern.
-/
theorem cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_sameSupport
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    {vars : List (Fin m)}
    (hsame : GeneratedParitySpecsSameSupportVars specs vars)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    GroupFrame.CNFClausesHaveCanonicalSupportVars
      (generatedParitySpecsCNF specs)
      vars := by
  intro c hc
  rw [generatedParitySpecsCNF_eq_bind] at hc
  rcases List.mem_bind.1 hc with ⟨spec, hspec, hmemSpec⟩
  cases spec with
  | mk specVars charge =>
      have hvars : specVars = vars := hsame (specVars, charge) hspec
      have hmemClauses :
          List.Mem c (clausesForVertex specVars charge) := by
        simpa [generatedParitySpecCNF] using hmemSpec
      subst specVars
      exact
        (GroupFrame.cnfClausesHaveCanonicalSupportVars_clausesForVertex
          (m := m) vars charge c hmemClauses).trans hnormal

/--
Every folded generated parity-spec list is semantically a parity-encoded class.
This theorem has no freshness or disjointness premise: those side conditions
belong to the executable residual-free extractor lane, not the declarative
per-assignment CNF/GF(2) equivalence lane.
-/
theorem class_of_generatedParitySpecs
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    ParityEncoded.Class m
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) := by
  rw [generatedParitySpecsCNF_eq_bind, generatedParitySpecsGF2_eq_map]
  induction specs with
  | nil =>
      simpa using (ParityEncoded.Class.empty (m := m))
  | cons spec specs ih =>
      cases spec with
      | mk vars charge =>
          have hatom :
              ParityEncoded.Class m
                (generatedParitySpecCNF (vars, charge))
                [generatedParitySpecGF2 (vars, charge)] := by
            exact
              ParityEncoded.Class.atom vars charge
                (clausesForVertex vars charge) (List.Perm.refl _)
          simpa [generatedParitySpecCNF, generatedParitySpecGF2] using
            ParityEncoded.Class.append hatom ih

/-- Any clause in a generated-spec CNF comes from one generated parity spec. -/
theorem mem_generatedParitySpecsCNF_imp_exists_spec
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    {c : CNFModel.Clause m}
    (hmem : List.Mem c (generatedParitySpecsCNF specs)) :
    exists spec : GeneratedParitySpec m,
      List.Mem spec specs /\ List.Mem c (generatedParitySpecCNF spec) := by
  rw [generatedParitySpecsCNF_eq_bind] at hmem
  exact List.mem_bind.1 hmem

/--
Generated CNF prefixes are clause-key disjoint from a new generated block when
the new block's canonical support key is fresh for every generated spec in the
prefix.
-/
theorem clauseKeysDisjoint_generatedParitySpecsCNF_of_freshCanonicalSupportKeys
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    {vars : List (Fin m)}
    {charge : Bool}
    (hfresh :
      forall spec : GeneratedParitySpec m,
        List.Mem spec specs ->
          Not (GroupFrame.canonicalSupportKeyForVars vars =
            GroupFrame.canonicalSupportKeyForVars spec.1)) :
    GroupFrame.CNFClauseKeysDisjoint
      (generatedParitySpecsCNF specs)
      (clausesForVertex vars charge) := by
  intro cf hcf cg hcg hkey
  rcases mem_generatedParitySpecsCNF_imp_exists_spec hcf with
    ⟨spec, hspec, hcfSpec⟩
  have hcfKey :
      canonicalClauseSupportKey cf =
        GroupFrame.canonicalSupportKeyForVars spec.1 :=
    GroupFrame.cnfClausesHaveCanonicalSupportKey_clausesForVertex
      (m := m) (vars := spec.1) (charge := spec.2) cf hcfSpec
  have hcgKey :
      canonicalClauseSupportKey cg =
        GroupFrame.canonicalSupportKeyForVars vars :=
    GroupFrame.cnfClausesHaveCanonicalSupportKey_clausesForVertex
      (m := m) (vars := vars) (charge := charge) cg hcg
  have hsupportKey :
      GroupFrame.canonicalSupportKeyForVars vars =
        GroupFrame.canonicalSupportKeyForVars spec.1 := by
    rw [← hcgKey, hkey, hcfKey]
  exact hfresh spec hspec hsupportKey

/-- Generated parity specs obtained from an incident-list Tseitin encoder. -/
def generatedParitySpecsFromIncident {m : Nat}
    (vertices : List Nat)
    (incident : Nat -> List (Fin m))
    (charge : Nat -> Bool) :
    List (GeneratedParitySpec m) :=
  vertices.map (fun v => (incident v, charge v))

/-- Incident-generated spec lists commute with snoc on the vertex list. -/
theorem generatedParitySpecsFromIncident_append_singleton
    {m : Nat}
    (vertices : List Nat)
    (v : Nat)
    (incident : Nat -> List (Fin m))
    (charge : Nat -> Bool) :
    generatedParitySpecsFromIncident (vertices ++ [v]) incident charge =
      generatedParitySpecsFromIncident vertices incident charge ++
        [(incident v, charge v)] := by
  simp [generatedParitySpecsFromIncident]

/--
The generated-spec CNF fold is definitionally aligned with the existing
incident-list Tseitin CNF encoder.
-/
theorem generatedParitySpecsCNF_fromIncident
    {n m : Nat}
    (incident : Nat -> List (Fin m))
    (charge : Nat -> Bool) :
    generatedParitySpecsCNF
        (generatedParitySpecsFromIncident (List.range n) incident charge) =
      tseitinClausesFromIncident n m incident charge := by
  simp [generatedParitySpecsFromIncident, generatedParitySpecsCNF,
    generatedParitySpecCNF, tseitinClausesFromIncident, List.foldl_map]

/--
The generated-spec GF(2) fold is definitionally aligned with the existing
incident-list direct parity encoder.
-/
theorem generatedParitySpecsGF2_fromIncident
    {n m : Nat}
    (incident : Nat -> List (Fin m))
    (charge : Nat -> Bool) :
    generatedParitySpecsGF2
        (generatedParitySpecsFromIncident (List.range n) incident charge) =
      tseitinParityFormulaFromIncident n m incident charge := by
  simp [generatedParitySpecsFromIncident, generatedParitySpecsGF2,
    generatedParitySpecGF2, tseitinParityFormulaFromIncident, List.foldl_map,
    foldl_append_singleton_eq_append_map]

/-- Generated parity specs obtained from a concrete graph encoding. -/
def generatedParitySpecsFromEncoding
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool) :
    List (GeneratedParitySpec
      (TseitinModel.GraphEncodingData.toGraph enc).m) :=
  let G := TseitinModel.GraphEncodingData.toGraph enc
  let hme := TseitinModel.m_eq_edges_length_of_encoding enc
  generatedParitySpecsFromIncident (List.range G.n) (incidentIndices G hme) charge

/-- The generated-spec CNF fold equals the existing graph-encoding CNF formula. -/
theorem generatedParitySpecsCNF_fromEncoding
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool) :
    generatedParitySpecsCNF
        (generatedParitySpecsFromEncoding enc charge) =
      TseitinCNFFormulaFromEncoding enc charge := by
  dsimp [generatedParitySpecsFromEncoding, TseitinCNFFormulaFromEncoding,
    TseitinCNFFormulaFromModel]
  exact generatedParitySpecsCNF_fromIncident
    (incidentIndices (TseitinModel.GraphEncodingData.toGraph enc)
      (TseitinModel.m_eq_edges_length_of_encoding enc))
    charge

/-- The generated-spec GF(2) fold equals the existing graph-encoding parity formula. -/
theorem generatedParitySpecsGF2_fromEncoding
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool) :
    generatedParitySpecsGF2
        (generatedParitySpecsFromEncoding enc charge) =
      TseitinParityFormulaFromEncoding enc charge := by
  dsimp [generatedParitySpecsFromEncoding, TseitinParityFormulaFromEncoding]
  exact generatedParitySpecsGF2_fromIncident
    (incidentIndices (TseitinModel.GraphEncodingData.toGraph enc)
      (TseitinModel.m_eq_edges_length_of_encoding enc))
    charge

/-- Generated parity specs for the derived directed cycle family. -/
def generatedParitySpecsForCycle (n : Nat) (hn : 1 < n) :
    List (GeneratedParitySpec
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m) :=
  generatedParitySpecsFromEncoding
    (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge

/--
Any arity-four generated parity expansion has at least one ordinary CNF clause.
This packages the existing exact length theorem in the constructor-friendly
`c :: tail` form used by generated-spec side-condition certificates.
-/
theorem clausesForVertex_exists_cons_of_length_four
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    (hlen : vars.length = 4) :
    exists c : CNFModel.Clause m,
      exists tail : CNFModel.CNF m,
        clausesForVertex vars charge = c :: tail := by
  have hlenClauses :
      (clausesForVertex vars charge).length = 8 :=
    clausesForVertex_length_of_length_four hlen
  cases hclauses : clausesForVertex vars charge with
  | nil =>
      rw [hclauses] at hlenClauses
      simp at hlenClauses
  | cons c tail =>
      exact Exists.intro c (Exists.intro tail rfl)

/--
Any generated parity expansion over at least one variable has at least one
ordinary CNF clause.  This is the arity-independent side-condition bridge used
by graph families whose vertex degrees are not four.
-/
theorem clausesForVertex_exists_cons_of_vars_ne_empty
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    (hvars : Not (vars = [])) :
    exists c : CNFModel.Clause m,
      exists tail : CNFModel.CNF m,
        clausesForVertex vars charge = c :: tail := by
  have hmem :
      exists row : List Bool,
        List.Mem (clauseForAssignment vars row)
          (clausesForVertex vars charge) := by
    cases charge with
    | false =>
        cases vars with
        | nil =>
            exact False.elim (hvars rfl)
        | cons v vs =>
            let row := true :: List.replicate vs.length false
            have hrowLen : row.length = (v :: vs).length := by
              simp [row]
            have hbad : (parity row == false) = false := by
              simp [row, parity_cons, parity_replicate_false]
            exact Exists.intro row
              (clauseForAssignment_mem_clausesForVertex_of_bad_parity
                hrowLen hbad)
    | true =>
        let row := List.replicate vars.length false
        have hrowLen : row.length = vars.length := by
          simp [row]
        have hbad : (parity row == true) = false := by
          simp [row, parity_replicate_false]
        exact Exists.intro row
          (clauseForAssignment_mem_clausesForVertex_of_bad_parity
            hrowLen hbad)
  cases hmem with
  | intro row hmemRow =>
      cases hclauses : clausesForVertex vars charge with
      | nil =>
          rw [hclauses] at hmemRow
          cases hmemRow
      | cons c tail =>
          exact Exists.intro c (Exists.intro tail rfl)

/--
If every bound list has at least one output element, binding cannot shrink the
outer list's length.  This is the small counting fact used to turn a generated
same-support CNF component into a safe charge-search bound.
-/
theorem length_le_bind_length_of_forall_exists_cons
    {alpha beta : Type} (xs : List alpha) (f : alpha -> List beta)
    (h :
      forall x : alpha, List.Mem x xs ->
        exists y : beta, exists ys : List beta, f x = y :: ys) :
    xs.length <= (xs.bind f).length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : exists y : beta, exists ys : List beta, f x = y :: ys :=
        h x (List.Mem.head xs)
      have htail :
          forall z : alpha, List.Mem z xs ->
            exists y : beta, exists ys : List beta, f z = y :: ys := by
        intro z hz
        exact h z (List.Mem.tail x hz)
      rcases hx with ⟨y, ys, hy⟩
      have hxs : xs.length <= (xs.bind f).length := ih htail
      calc
        (x :: xs).length = Nat.succ xs.length := rfl
        _ <= Nat.succ (ys.length + (xs.bind f).length) := by
          exact Nat.succ_le_succ
            (Nat.le_trans hxs (Nat.le_add_left (xs.bind f).length ys.length))
        _ = ((x :: xs).bind f).length := by
          simp [List.bind, hy]

/--
For a nonempty support, the number of generated same-support parity blocks is
bounded by the number of ordinary clauses in their CNF expansion.
-/
theorem generatedParitySpecsForSupportCharges_length_le_cnf_length_of_vars_ne_empty
    {m : Nat} {vars : List (Fin m)}
    (charges : List Bool)
    (hvars : vars ≠ []) :
    charges.length <=
      (generatedParitySpecsCNF
        (generatedParitySpecsForSupportCharges vars charges)).length := by
  rw [generatedParitySpecsCNF_eq_bind]
  have hspec :=
    length_le_bind_length_of_forall_exists_cons
      (generatedParitySpecsForSupportCharges vars charges)
      generatedParitySpecCNF
      (by
        intro spec hspec
        unfold generatedParitySpecsForSupportCharges at hspec
        rcases List.mem_map.1 hspec with ⟨charge, _hcharge, hspec_eq⟩
        cases hspec_eq
        simpa [generatedParitySpecCNF] using
          clausesForVertex_exists_cons_of_vars_ne_empty
            (vars := vars) (charge := charge) hvars)
  simpa [generatedParitySpecsForSupportCharges] using hspec

/--
The component-length version of the same bound, transported across clause
permutation.  This removes the need for an externally supplied charge bound
when the component is known to be a nonempty-support generated same-support
CNF.
-/
theorem charges_length_le_of_perm_generatedParitySpecsForSupportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : vars ≠ [])
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges))) :
    charges.length <= target.length := by
  have hle :=
    generatedParitySpecsForSupportCharges_length_le_cnf_length_of_vars_ne_empty
      (vars := vars) charges hvars
  have hlen :
      target.length =
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)).length :=
    hperm.length_eq
  simpa [hlen] using hle

/--
Positive vertex degree supplies the nonempty generated CNF-block witness needed
by incident-list generated-spec certificates.
-/
theorem incidentClausesForVertex_exists_cons_of_degree_pos
    (G : TseitinModel.Graph)
    (hme : TseitinModel.m_eq_edges_length G)
    (v : Nat)
    (charge : Bool)
    (hdeg : 0 < TseitinModel.degree G v) :
    exists c : CNFModel.Clause G.m,
      exists tail : CNFModel.CNF G.m,
        clausesForVertex (incidentIndices G hme v) charge = c :: tail := by
  apply clausesForVertex_exists_cons_of_vars_ne_empty
  intro hnil
  have hlen := incidentIndices_length_eq_degree G hme v
  have hzero : (incidentIndices G hme v).length = 0 := by
    simp [hnil]
  omega

/-- Every vertex incident-index list in the derived directed cycle has arity four. -/
theorem cycleIncidentIndices_length_eq_four
    (n v : Nat)
    (hn : 1 < n)
    (hv : v < n) :
    (incidentIndices
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn))
      (TseitinModel.m_eq_edges_length_of_encoding
        (TseitinModel.encoding_cycle_derived n hn))
      v).length = 4 := by
  have hdeg :
      TseitinModel.degree
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)) v = 4 := by
    apply TseitinModel.cycle_degree_eq_four
    simpa [TseitinModel.encoding_cycle_derived, TseitinModel.encoding_cycle_nle,
      TseitinModel.encoding_cycle, TseitinModel.GraphEncodingData.toGraph] using hv
  have hlen := incidentIndices_length_eq_degree
    (TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived n hn))
    (TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_cycle_derived n hn)) v
  exact hlen.trans hdeg

/--
Every generated vertex block in the derived directed cycle has a nonempty CNF
expansion.  Future cycle freshness proofs can use this directly for the
`GeneratedCanonicalKeyFreshSpecList.snoc` nonempty witness.
-/
theorem cycleClausesForVertex_exists_cons
    (n v : Nat)
    (hn : 1 < n)
    (hv : v < n) :
    exists c : CNFModel.Clause
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m,
      exists tail : CNFModel.CNF
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m,
        clausesForVertex
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_cycle_derived n hn))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_cycle_derived n hn))
            v)
          (cycleRootCharge v) = c :: tail :=
  clausesForVertex_exists_cons_of_length_four
    (cycleIncidentIndices_length_eq_four n v hn hv)

private theorem sortByBool_eq_self_of_pairwise
    {alpha : Type}
    (le : alpha -> alpha -> Bool)
    {xs : List alpha}
    (hpair : List.Pairwise (fun a b => le a b = true) xs) :
    sortByBool le xs = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [sortByBool, insertSortedBy]
      | cons y ys =>
          have hparts := List.pairwise_cons.1 hpair
          have hxy : le x y = true := hparts.1 y (List.Mem.head ys)
          have htail :
              List.Pairwise (fun a b => le a b = true) (y :: ys) :=
            hparts.2
          rw [sortByBool]
          rw [ih htail]
          simp [insertSortedBy, hxy]

private theorem eraseDups_loop_eq_reverse_append_of_nodup_disjoint
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall (xs acc : List alpha),
      xs.Nodup ->
      (forall x : alpha, List.Mem x xs -> Not (List.Mem x acc)) ->
      List.eraseDups.loop xs acc = acc.reverse ++ xs := by
  intro xs
  induction xs with
  | nil =>
      intro acc _hnodup _hdisjoint
      simp [List.eraseDups.loop]
  | cons x xs ih =>
      intro acc hnodup hdisjoint
      have hparts := List.nodup_cons.1 hnodup
      have hnotTail : Not (List.Mem x xs) := hparts.1
      have htail : xs.Nodup := hparts.2
      have hnotAcc : Not (List.Mem x acc) :=
        hdisjoint x (List.Mem.head xs)
      have helem : List.elem x acc = false := by
        cases hval : List.elem x acc with
        | false =>
            rfl
        | true =>
            have hmem : List.Mem x acc :=
              (GroupFrame.elem_eq_true_iff_mem x acc).1 hval
            exact False.elim (hnotAcc hmem)
      have hdisjointTail :
          forall y : alpha, List.Mem y xs -> Not (List.Mem y (x :: acc)) := by
        intro y hy hmem
        cases hmem with
        | head =>
            exact hnotTail (by simpa using hy)
        | tail _ hacc =>
            exact hdisjoint y (List.Mem.tail x hy) hacc
      have hloop := ih (x :: acc) htail hdisjointTail
      rw [List.eraseDups.loop]
      rw [helem]
      rw [hloop]
      simp [List.append_assoc]

private theorem eraseDups_eq_self_of_nodup
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {xs : List alpha}
    (hnodup : xs.Nodup) :
    xs.eraseDups = xs := by
  have hloop :=
    eraseDups_loop_eq_reverse_append_of_nodup_disjoint
      (xs := xs) (acc := []) hnodup
      (by
        intro _x _hx hnil
        cases hnil)
  simpa [List.eraseDups] using hloop

/-- The canonical finite-index enumeration is strictly increasing by value. -/
theorem allFin_pairwise_val_lt (m : Nat) :
    List.Pairwise (fun a b : Fin m => a.val < b.val) (allFin m) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  rw [allFin_get_val m i.val i.isLt, allFin_get_val m j.val j.isLt]
  exact hij

/--
Every filtered `allFin` list is already in the canonical support order used by
the executable recognizer: filtering preserves increasing finite-index order
and `allFin` has no duplicates.
-/
theorem allFin_filter_varsInCanonicalSupportOrder
    {m : Nat}
    (p : Fin m -> Bool) :
    GroupFrame.VarsInCanonicalSupportOrder ((allFin m).filter p) := by
  have hstrict :
      List.Pairwise (fun a b : Fin m => a.val < b.val)
        ((allFin m).filter p) :=
    List.Pairwise.sublist (List.filter_sublist (p := p) (allFin m))
      (allFin_pairwise_val_lt m)
  have hle :
      List.Pairwise
        (fun a b : Fin m =>
          (fun a b : Fin m => decide (a.val <= b.val)) a b = true)
        ((allFin m).filter p) :=
    hstrict.imp (fun {a b} hlt => decide_eq_true (Nat.le_of_lt hlt))
  have hsort :=
    sortByBool_eq_self_of_pairwise
      (fun a b : Fin m => decide (a.val <= b.val)) hle
  have hnodup : ((allFin m).filter p).Nodup :=
    (allFin_nodup m).filter p
  unfold GroupFrame.VarsInCanonicalSupportOrder sortFinByVal
  rw [hsort]
  exact eraseDups_eq_self_of_nodup hnodup

/--
Incident-index lists generated from concrete graph encodings are in canonical
support order because they are filters of `allFin`.
-/
theorem incidentIndices_varsInCanonicalSupportOrder
    (G : TseitinModel.Graph)
    (hm : G.m = G.edges.length)
    (v : Nat) :
    GroupFrame.VarsInCanonicalSupportOrder (incidentIndices G hm v) := by
  unfold incidentIndices
  exact allFin_filter_varsInCanonicalSupportOrder
    (fun i : Fin G.m => TseitinModel.UEdge.incident (edgeAt G hm i) v)

/--
Derived-cycle incident-index lists satisfy the normal-order side condition
needed by generated canonical-key freshness certificates.
-/
theorem cycleIncidentIndices_varsInCanonicalSupportOrder
    (n v : Nat)
    (hn : 1 < n) :
    GroupFrame.VarsInCanonicalSupportOrder
      (incidentIndices
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn))
        (TseitinModel.m_eq_edges_length_of_encoding
          (TseitinModel.encoding_cycle_derived n hn))
        v) :=
  incidentIndices_varsInCanonicalSupportOrder
    (TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived n hn))
    (TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_cycle_derived n hn))
    v

private theorem bindPairRange_length {alpha : Type}
    (left right : Nat -> alpha) (n : Nat) :
    ((List.range n).bind (fun i => [left i, right i])).length = 2 * n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ]
      simp [ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem bindPairRange_getElem?_even {alpha : Type}
    (left right : Nat -> alpha) :
    forall (n v : Nat), v < n ->
      ((List.range n).bind (fun i => [left i, right i]))[2 * v]? =
        some (left v) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      omega
  | succ n ih =>
      intro v hv
      by_cases hvn : v < n
      case pos =>
        rw [List.range_succ]
        rw [List.bind_append]
        have hidx :
            2 * v < ((List.range n).bind (fun i => [left i, right i])).length := by
          rw [bindPairRange_length]
          omega
        simp [List.getElem?_append, hidx, ih v hvn]
      case neg =>
        have hvEq : v = n := by
          omega
        subst v
        rw [List.range_succ]
        rw [List.bind_append]
        have hnotIdx :
            Not (2 * n < ((List.range n).bind (fun i => [left i, right i])).length) := by
          rw [bindPairRange_length]
          omega
        rw [List.getElem?_append]
        rw [if_neg hnotIdx]
        simp [bindPairRange_length]

private theorem bindPairRange_getElem?_odd {alpha : Type}
    (left right : Nat -> alpha) :
    forall (n v : Nat), v < n ->
      ((List.range n).bind (fun i => [left i, right i]))[2 * v + 1]? =
        some (right v) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      omega
  | succ n ih =>
      intro v hv
      by_cases hvn : v < n
      case pos =>
        rw [List.range_succ]
        rw [List.bind_append]
        have hidx :
            2 * v + 1 < ((List.range n).bind (fun i => [left i, right i])).length := by
          rw [bindPairRange_length]
          omega
        simp [List.getElem?_append, hidx, ih v hvn]
      case neg =>
        have hvEq : v = n := by
          omega
        subst v
        rw [List.range_succ]
        rw [List.bind_append]
        have hnotIdx :
            Not (2 * n + 1 <
              ((List.range n).bind (fun i => [left i, right i])).length) := by
          rw [bindPairRange_length]
          omega
        rw [List.getElem?_append]
        rw [if_neg hnotIdx]
        simp [bindPairRange_length]

private theorem bindQuadRange_length {alpha : Type}
    (a b c d : Nat -> alpha) (n : Nat) :
    ((List.range n).bind (fun i => [a i, b i, c i, d i])).length = 4 * n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ]
      simp [ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem bindQuadRange_getElem?_zero {alpha : Type}
    (a b c d : Nat -> alpha) :
    forall (n v : Nat), v < n ->
      ((List.range n).bind (fun i => [a i, b i, c i, d i]))[4 * v]? =
        some (a v) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      omega
  | succ n ih =>
      intro v hv
      by_cases hvn : v < n
      case pos =>
        rw [List.range_succ]
        rw [List.bind_append]
        have hidx :
            4 * v < ((List.range n).bind (fun i => [a i, b i, c i, d i])).length := by
          rw [bindQuadRange_length]
          omega
        simp [List.getElem?_append, hidx, ih v hvn]
      case neg =>
        have hvEq : v = n := by
          omega
        subst v
        rw [List.range_succ]
        rw [List.bind_append]
        have hnotIdx :
            Not (4 * n < ((List.range n).bind (fun i => [a i, b i, c i, d i])).length) := by
          rw [bindQuadRange_length]
          omega
        rw [List.getElem?_append]
        rw [if_neg hnotIdx]
        simp [bindQuadRange_length]

private theorem bindQuadRange_getElem?_two {alpha : Type}
    (a b c d : Nat -> alpha) :
    forall (n v : Nat), v < n ->
      ((List.range n).bind (fun i => [a i, b i, c i, d i]))[4 * v + 2]? =
        some (c v) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      omega
  | succ n ih =>
      intro v hv
      by_cases hvn : v < n
      case pos =>
        rw [List.range_succ]
        rw [List.bind_append]
        have hidx :
            4 * v + 2 < ((List.range n).bind (fun i => [a i, b i, c i, d i])).length := by
          rw [bindQuadRange_length]
          omega
        simp [List.getElem?_append, hidx, ih v hvn]
      case neg =>
        have hvEq : v = n := by
          omega
        subst v
        rw [List.range_succ]
        rw [List.bind_append]
        have hnotIdx :
            Not (4 * n + 2 <
              ((List.range n).bind (fun i => [a i, b i, c i, d i])).length) := by
          rw [bindQuadRange_length]
          omega
        rw [List.getElem?_append]
        rw [if_neg hnotIdx]
        simp [bindQuadRange_length]

/-- Canonical support keys for variable lists contain exactly the variable values. -/
theorem mem_canonicalSupportKeyForVars_iff {m : Nat}
    (vars : List (Fin m)) (key : Nat) :
    List.Mem key (GroupFrame.canonicalSupportKeyForVars vars) <->
      exists v : Fin m, List.Mem v vars /\ v.val = key := by
  unfold GroupFrame.canonicalSupportKeyForVars
  constructor
  case mp =>
    intro hmem
    cases List.mem_map.1 hmem with
    | intro v hvAnd =>
        cases hvAnd with
        | intro hv hval =>
            have hsort : List.Mem v (sortFinByVal vars) :=
              (GroupFrame.mem_eraseDups_iff v (sortFinByVal vars)).1 hv
            exact Exists.intro v (And.intro
              ((GroupFrame.mem_sortByBool_iff
                (fun a b : Fin m => decide (a.val <= b.val)) v vars).1 hsort)
              hval)
  case mpr =>
    intro h
    cases h with
    | intro v hvAnd =>
        cases hvAnd with
        | intro hv hval =>
            apply List.mem_map.2
            exact Exists.intro v (And.intro
              ((GroupFrame.mem_eraseDups_iff v (sortFinByVal vars)).2
                ((GroupFrame.mem_sortByBool_iff
                  (fun a b : Fin m => decide (a.val <= b.val)) v vars).2 hv))
              hval)

/-- A finite edge index is in a vertex's incident index list when its edge is incident. -/
theorem incidentIndex_mem_of_incident
    {G : TseitinModel.Graph} {hm : G.m = G.edges.length}
    {i : Fin G.m} {v : Nat}
    (hinc : TseitinModel.UEdge.incident (edgeAt G hm i) v = true) :
    List.Mem i (incidentIndices G hm v) := by
  unfold incidentIndices
  apply List.mem_filter.2
  exact And.intro (mem_allFin i) hinc

/-- Incident index-list membership exposes the underlying executable incident test. -/
theorem incident_of_mem_incidentIndex
    {G : TseitinModel.Graph} {hm : G.m = G.edges.length}
    {i : Fin G.m} {v : Nat}
    (hmem : List.Mem i (incidentIndices G hm v)) :
    TseitinModel.UEdge.incident (edgeAt G hm i) v = true := by
  unfold incidentIndices at hmem
  exact (List.mem_filter.1 hmem).2

/-- The derived directed cycle graph has two edge variables per cycle position. -/
theorem cycleGraph_m_eq_two_mul
    (n : Nat) (hn : 1 < n) :
    (TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived n hn)).m = 2 * n := by
  simp [TseitinModel.encoding_cycle_derived,
    TseitinModel.encoding_cycle_nle, TseitinModel.encoding_cycle,
    TseitinModel.GraphEncodingData.toGraph,
    TseitinModel.cycle_edges_length]

/-- The even directed edge index for a cycle vertex is in range. -/
theorem cycleEvenEdgeIndex_lt
    (n v : Nat) (hn : 1 < n) (hv : v < n) :
    2 * v <
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m := by
  rw [cycleGraph_m_eq_two_mul n hn]
  omega

/-- The odd directed edge index for a cycle vertex is in range. -/
theorem cycleOddEdgeIndex_lt
    (n v : Nat) (hn : 1 < n) (hv : v < n) :
    2 * v + 1 <
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m := by
  rw [cycleGraph_m_eq_two_mul n hn]
  omega

/-- The derived `circulant12` graph has four edge variables per vertex position. -/
theorem circulant12Graph_m_eq_four_mul
    (n : Nat) (hn : 2 < n) :
    (TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_circulant12_derived n hn)).m = 4 * n := by
  simp [TseitinModel.encoding_circulant12_derived,
    TseitinModel.GraphEncodingData.toGraph,
    TseitinModel.circulant12_edges_length]

/-- The forward-one edge index for a `circulant12` vertex is in range. -/
theorem circulant12ForwardOneEdgeIndex_lt
    (n u : Nat) (hn : 2 < n) (hu : u < n) :
    4 * u <
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_circulant12_derived n hn)).m := by
  rw [circulant12Graph_m_eq_four_mul n hn]
  omega

/-- The forward-two edge index for a `circulant12` vertex is in range. -/
theorem circulant12ForwardTwoEdgeIndex_lt
    (n u : Nat) (hn : 2 < n) (hu : u < n) :
    4 * u + 2 <
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_circulant12_derived n hn)).m := by
  rw [circulant12Graph_m_eq_four_mul n hn]
  omega

/--
Even directed edge variables in the derived cycle are the forward edges
`v -> (v + 1) % n`.
-/
theorem cycleEdgeAt_even_eq
    (n v : Nat) (hn : 1 < n) (hv : v < n) :
    let G := TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived n hn)
    let hme := TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_cycle_derived n hn)
    edgeAt G hme (Fin.mk (2 * v) (cycleEvenEdgeIndex_lt n v hn hv)) =
      TseitinModel.UEdge.mk v ((v + 1) % n) := by
  dsimp
  unfold edgeAt
  simp [TseitinModel.encoding_cycle_derived,
    TseitinModel.encoding_cycle_nle, TseitinModel.encoding_cycle,
    TseitinModel.GraphEncodingData.toGraph, List.get_eq_getElem]
  let edges := ((List.range n).bind fun i =>
        [TseitinModel.UEdge.mk i ((i + 1) % n),
          TseitinModel.UEdge.mk ((i + 1) % n) i])
  have hget? :
      edges[2 * v]? = some (TseitinModel.UEdge.mk v ((v + 1) % n)) := by
    dsimp [edges]
    exact bindPairRange_getElem?_even
      (fun i => TseitinModel.UEdge.mk i ((i + 1) % n))
      (fun i => TseitinModel.UEdge.mk ((i + 1) % n) i)
      n v hv
  have hlen : 2 * v < edges.length := by
    dsimp [edges]
    rw [bindPairRange_length]
    omega
  have hsome := List.getElem?_eq_getElem (l := edges) hlen
  have hsomeEq :
      some edges[2 * v] =
        some (TseitinModel.UEdge.mk v ((v + 1) % n)) := by
    exact hsome.symm.trans hget?
  have hget :
      edges[2 * v] = TseitinModel.UEdge.mk v ((v + 1) % n) :=
    Option.some.inj hsomeEq
  simpa [edges] using hget

/--
Odd directed edge variables in the derived cycle are the reverse edges
`(v + 1) % n -> v`.
-/
theorem cycleEdgeAt_odd_eq
    (n v : Nat) (hn : 1 < n) (hv : v < n) :
    let G := TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived n hn)
    let hme := TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_cycle_derived n hn)
    edgeAt G hme (Fin.mk (2 * v + 1) (cycleOddEdgeIndex_lt n v hn hv)) =
      TseitinModel.UEdge.mk ((v + 1) % n) v := by
  dsimp
  unfold edgeAt
  simp [TseitinModel.encoding_cycle_derived,
    TseitinModel.encoding_cycle_nle, TseitinModel.encoding_cycle,
    TseitinModel.GraphEncodingData.toGraph, List.get_eq_getElem]
  let edges := ((List.range n).bind fun i =>
        [TseitinModel.UEdge.mk i ((i + 1) % n),
          TseitinModel.UEdge.mk ((i + 1) % n) i])
  have hget? :
      edges[2 * v + 1]? = some (TseitinModel.UEdge.mk ((v + 1) % n) v) := by
    dsimp [edges]
    exact bindPairRange_getElem?_odd
      (fun i => TseitinModel.UEdge.mk i ((i + 1) % n))
      (fun i => TseitinModel.UEdge.mk ((i + 1) % n) i)
      n v hv
  have hlen : 2 * v + 1 < edges.length := by
    dsimp [edges]
    rw [bindPairRange_length]
    omega
  have hsome := List.getElem?_eq_getElem (l := edges) hlen
  have hsomeEq :
      some edges[2 * v + 1] =
        some (TseitinModel.UEdge.mk ((v + 1) % n) v) := by
    exact hsome.symm.trans hget?
  have hget :
      edges[2 * v + 1] =
        TseitinModel.UEdge.mk ((v + 1) % n) v :=
    Option.some.inj hsomeEq
  simpa [edges] using hget

/--
The first edge in each `circulant12` block is the forward-one edge
`u -> (u + 1) % n`.
-/
theorem circulant12EdgeAt_forwardOne_eq
    (n u : Nat) (hn : 2 < n) (hu : u < n) :
    let G := TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_circulant12_derived n hn)
    let hme := TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_circulant12_derived n hn)
    edgeAt G hme (Fin.mk (4 * u) (circulant12ForwardOneEdgeIndex_lt n u hn hu)) =
      TseitinModel.UEdge.mk u ((u + 1) % n) := by
  dsimp
  unfold edgeAt
  simp [TseitinModel.encoding_circulant12_derived,
    TseitinModel.GraphEncodingData.toGraph, TseitinModel.circulant12_edges,
    TseitinModel.circulant12_edge_block, List.get_eq_getElem]
  let edges := ((List.range n).bind fun i =>
        [TseitinModel.UEdge.mk i ((i + 1) % n),
          TseitinModel.UEdge.mk ((i + 1) % n) i,
          TseitinModel.UEdge.mk i ((i + 2) % n),
          TseitinModel.UEdge.mk ((i + 2) % n) i])
  have hget? :
      edges[4 * u]? = some (TseitinModel.UEdge.mk u ((u + 1) % n)) := by
    dsimp [edges]
    exact bindQuadRange_getElem?_zero
      (fun i => TseitinModel.UEdge.mk i ((i + 1) % n))
      (fun i => TseitinModel.UEdge.mk ((i + 1) % n) i)
      (fun i => TseitinModel.UEdge.mk i ((i + 2) % n))
      (fun i => TseitinModel.UEdge.mk ((i + 2) % n) i)
      n u hu
  have hlen : 4 * u < edges.length := by
    dsimp [edges]
    rw [bindQuadRange_length]
    omega
  have hsome := List.getElem?_eq_getElem (l := edges) hlen
  have hsomeEq :
      some edges[4 * u] =
        some (TseitinModel.UEdge.mk u ((u + 1) % n)) := by
    exact hsome.symm.trans hget?
  have hget :
      edges[4 * u] = TseitinModel.UEdge.mk u ((u + 1) % n) :=
    Option.some.inj hsomeEq
  simpa [edges] using hget

/--
The third edge in each `circulant12` block is the forward-two edge
`u -> (u + 2) % n`.
-/
theorem circulant12EdgeAt_forwardTwo_eq
    (n u : Nat) (hn : 2 < n) (hu : u < n) :
    let G := TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_circulant12_derived n hn)
    let hme := TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_circulant12_derived n hn)
    edgeAt G hme (Fin.mk (4 * u + 2) (circulant12ForwardTwoEdgeIndex_lt n u hn hu)) =
      TseitinModel.UEdge.mk u ((u + 2) % n) := by
  dsimp
  unfold edgeAt
  simp [TseitinModel.encoding_circulant12_derived,
    TseitinModel.GraphEncodingData.toGraph, TseitinModel.circulant12_edges,
    TseitinModel.circulant12_edge_block, List.get_eq_getElem]
  let edges := ((List.range n).bind fun i =>
        [TseitinModel.UEdge.mk i ((i + 1) % n),
          TseitinModel.UEdge.mk ((i + 1) % n) i,
          TseitinModel.UEdge.mk i ((i + 2) % n),
          TseitinModel.UEdge.mk ((i + 2) % n) i])
  have hget? :
      edges[4 * u + 2]? = some (TseitinModel.UEdge.mk u ((u + 2) % n)) := by
    dsimp [edges]
    exact bindQuadRange_getElem?_two
      (fun i => TseitinModel.UEdge.mk i ((i + 1) % n))
      (fun i => TseitinModel.UEdge.mk ((i + 1) % n) i)
      (fun i => TseitinModel.UEdge.mk i ((i + 2) % n))
      (fun i => TseitinModel.UEdge.mk ((i + 2) % n) i)
      n u hu
  have hlen : 4 * u + 2 < edges.length := by
    dsimp [edges]
    rw [bindQuadRange_length]
    omega
  have hsome := List.getElem?_eq_getElem (l := edges) hlen
  have hsomeEq :
      some edges[4 * u + 2] =
        some (TseitinModel.UEdge.mk u ((u + 2) % n)) := by
    exact hsome.symm.trans hget?
  have hget :
      edges[4 * u + 2] = TseitinModel.UEdge.mk u ((u + 2) % n) :=
    Option.some.inj hsomeEq
  simpa [edges] using hget

/-- Each cycle vertex key contains its forward even directed-edge index. -/
theorem cycleCanonicalIncidentSupportKey_mem_even
    (n u : Nat) (hn : 1 < n) (hu : u < n) :
    List.Mem (2 * u)
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          u)) := by
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_cycle_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_cycle_derived n hn)
  let idx : Fin G.m := Fin.mk (2 * u) (cycleEvenEdgeIndex_lt n u hn hu)
  have hidxmem : List.Mem idx (incidentIndices G hme u) := by
    apply incidentIndex_mem_of_incident
    have hedge : edgeAt G hme idx = TseitinModel.UEdge.mk u ((u + 1) % n) := by
      dsimp [G, hme, idx]
      exact cycleEdgeAt_even_eq n u hn hu
    rw [hedge]
    simp [TseitinModel.UEdge.incident]
  apply (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme u) (2 * u)).2
  exact Exists.intro idx (And.intro hidxmem rfl)

/-- Each cycle vertex key contains its reverse odd directed-edge index. -/
theorem cycleCanonicalIncidentSupportKey_mem_odd
    (n u : Nat) (hn : 1 < n) (hu : u < n) :
    List.Mem (2 * u + 1)
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          u)) := by
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_cycle_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_cycle_derived n hn)
  let idx : Fin G.m := Fin.mk (2 * u + 1) (cycleOddEdgeIndex_lt n u hn hu)
  have hidxmem : List.Mem idx (incidentIndices G hme u) := by
    apply incidentIndex_mem_of_incident
    have hedge : edgeAt G hme idx = TseitinModel.UEdge.mk ((u + 1) % n) u := by
      dsimp [G, hme, idx]
      exact cycleEdgeAt_odd_eq n u hn hu
    rw [hedge]
    simp [TseitinModel.UEdge.incident]
  apply (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme u) (2 * u + 1)).2
  exact Exists.intro idx (And.intro hidxmem rfl)

/-- Each `circulant12` vertex key contains its forward-one edge index. -/
theorem circulant12CanonicalIncidentSupportKey_mem_forwardOne
    (n u : Nat) (hn : 2 < n) (hu : u < n) :
    List.Mem (4 * u)
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_circulant12_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_circulant12_derived n hn))
          u)) := by
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_circulant12_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_circulant12_derived n hn)
  let idx : Fin G.m := Fin.mk (4 * u) (circulant12ForwardOneEdgeIndex_lt n u hn hu)
  have hidxmem : List.Mem idx (incidentIndices G hme u) := by
    apply incidentIndex_mem_of_incident
    have hedge : edgeAt G hme idx = TseitinModel.UEdge.mk u ((u + 1) % n) := by
      dsimp [G, hme, idx]
      exact circulant12EdgeAt_forwardOne_eq n u hn hu
    rw [hedge]
    simp [TseitinModel.UEdge.incident]
  apply (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme u) (4 * u)).2
  exact Exists.intro idx (And.intro hidxmem rfl)

/-- Each `circulant12` vertex key contains its forward-two edge index. -/
theorem circulant12CanonicalIncidentSupportKey_mem_forwardTwo
    (n u : Nat) (hn : 2 < n) (hu : u < n) :
    List.Mem (4 * u + 2)
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_circulant12_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_circulant12_derived n hn))
          u)) := by
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_circulant12_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_circulant12_derived n hn)
  let idx : Fin G.m := Fin.mk (4 * u + 2) (circulant12ForwardTwoEdgeIndex_lt n u hn hu)
  have hidxmem : List.Mem idx (incidentIndices G hme u) := by
    apply incidentIndex_mem_of_incident
    have hedge : edgeAt G hme idx = TseitinModel.UEdge.mk u ((u + 2) % n) := by
      dsimp [G, hme, idx]
      exact circulant12EdgeAt_forwardTwo_eq n u hn hu
    rw [hedge]
    simp [TseitinModel.UEdge.incident]
  apply (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme u) (4 * u + 2)).2
  exact Exists.intro idx (And.intro hidxmem rfl)

/--
An even cycle edge index can occur in another vertex's canonical incident key
only at an endpoint of that edge.
-/
theorem cycleCanonicalIncidentSupportKey_not_mem_even_of_not_endpoint
    (n u v : Nat) (hn : 1 < n) (hu : u < n)
    (hnotLeft : Not (u = v))
    (hnotRight : Not (((u + 1) % n) = v)) :
    Not
      (List.Mem (2 * u)
        (GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_cycle_derived n hn))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_cycle_derived n hn))
            v))) := by
  intro hmem
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_cycle_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_cycle_derived n hn)
  have hex :=
    (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme v) (2 * u)).1 hmem
  cases hex with
  | intro idx hidxAnd =>
      cases hidxAnd with
      | intro hidxmem hidxval =>
          let edgeIdx : Fin G.m := Fin.mk (2 * u) (by
            dsimp [G]
            exact cycleEvenEdgeIndex_lt n u hn hu)
          have hidxEq : idx = edgeIdx := by
            apply Fin.ext
            exact hidxval
          have hinc := incident_of_mem_incidentIndex hidxmem
          rw [hidxEq] at hinc
          have hedge : edgeAt G hme edgeIdx = TseitinModel.UEdge.mk u ((u + 1) % n) := by
            dsimp [G, hme, edgeIdx]
            exact cycleEdgeAt_even_eq n u hn hu
          rw [hedge] at hinc
          simp [TseitinModel.UEdge.incident, hnotLeft, hnotRight] at hinc

/--
An odd cycle edge index can occur in another vertex's canonical incident key
only at an endpoint of that edge.
-/
theorem cycleCanonicalIncidentSupportKey_not_mem_odd_of_not_endpoint
    (n u v : Nat) (hn : 1 < n) (hu : u < n)
    (hnotLeft : Not (u = v))
    (hnotRight : Not (((u + 1) % n) = v)) :
    Not
      (List.Mem (2 * u + 1)
        (GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_cycle_derived n hn))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_cycle_derived n hn))
            v))) := by
  intro hmem
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_cycle_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_cycle_derived n hn)
  have hex :=
    (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme v) (2 * u + 1)).1 hmem
  cases hex with
  | intro idx hidxAnd =>
      cases hidxAnd with
      | intro hidxmem hidxval =>
          let edgeIdx : Fin G.m := Fin.mk (2 * u + 1) (by
            dsimp [G]
            exact cycleOddEdgeIndex_lt n u hn hu)
          have hidxEq : idx = edgeIdx := by
            apply Fin.ext
            exact hidxval
          have hinc := incident_of_mem_incidentIndex hidxmem
          rw [hidxEq] at hinc
          have hedge : edgeAt G hme edgeIdx = TseitinModel.UEdge.mk ((u + 1) % n) u := by
            dsimp [G, hme, edgeIdx]
            exact cycleEdgeAt_odd_eq n u hn hu
          rw [hedge] at hinc
          simp [TseitinModel.UEdge.incident, hnotLeft, hnotRight] at hinc

/--
A `circulant12` forward-one edge index can occur in another vertex's canonical
incident key only at an endpoint of that edge.
-/
theorem circulant12CanonicalIncidentSupportKey_not_mem_forwardOne_of_not_endpoint
    (n u v : Nat) (hn : 2 < n) (hu : u < n)
    (hnotLeft : Not (u = v))
    (hnotRight : Not (((u + 1) % n) = v)) :
    Not
      (List.Mem (4 * u)
        (GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_circulant12_derived n hn))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_circulant12_derived n hn))
            v))) := by
  intro hmem
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_circulant12_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_circulant12_derived n hn)
  have hex :=
    (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme v) (4 * u)).1 hmem
  cases hex with
  | intro idx hidxAnd =>
      cases hidxAnd with
      | intro hidxmem hidxval =>
          let edgeIdx : Fin G.m := Fin.mk (4 * u) (by
            dsimp [G]
            exact circulant12ForwardOneEdgeIndex_lt n u hn hu)
          have hidxEq : idx = edgeIdx := by
            apply Fin.ext
            exact hidxval
          have hinc := incident_of_mem_incidentIndex hidxmem
          rw [hidxEq] at hinc
          have hedge : edgeAt G hme edgeIdx = TseitinModel.UEdge.mk u ((u + 1) % n) := by
            dsimp [G, hme, edgeIdx]
            exact circulant12EdgeAt_forwardOne_eq n u hn hu
          rw [hedge] at hinc
          simp [TseitinModel.UEdge.incident, hnotLeft, hnotRight] at hinc

/--
A `circulant12` forward-two edge index can occur in another vertex's canonical
incident key only at an endpoint of that edge.
-/
theorem circulant12CanonicalIncidentSupportKey_not_mem_forwardTwo_of_not_endpoint
    (n u v : Nat) (hn : 2 < n) (hu : u < n)
    (hnotLeft : Not (u = v))
    (hnotRight : Not (((u + 2) % n) = v)) :
    Not
      (List.Mem (4 * u + 2)
        (GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_circulant12_derived n hn))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_circulant12_derived n hn))
            v))) := by
  intro hmem
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_circulant12_derived n hn)
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_circulant12_derived n hn)
  have hex :=
    (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme v) (4 * u + 2)).1 hmem
  cases hex with
  | intro idx hidxAnd =>
      cases hidxAnd with
      | intro hidxmem hidxval =>
          let edgeIdx : Fin G.m := Fin.mk (4 * u + 2) (by
            dsimp [G]
            exact circulant12ForwardTwoEdgeIndex_lt n u hn hu)
          have hidxEq : idx = edgeIdx := by
            apply Fin.ext
            exact hidxval
          have hinc := incident_of_mem_incidentIndex hidxmem
          rw [hidxEq] at hinc
          have hedge : edgeAt G hme edgeIdx = TseitinModel.UEdge.mk u ((u + 2) % n) := by
            dsimp [G, hme, edgeIdx]
            exact circulant12EdgeAt_forwardTwo_eq n u hn hu
          rw [hedge] at hinc
          simp [TseitinModel.UEdge.incident, hnotLeft, hnotRight] at hinc

/--
If `v` is not an endpoint of cycle edge `u`, then edge index `2*u`
separates the canonical incident-support keys for `u` and `v`.
-/
theorem cycleCanonicalIncidentSupportKeys_ne_of_not_endpoint
    (n u v : Nat) (hn : 1 < n) (hu : u < n)
    (hnotLeft : Not (u = v))
    (hnotRight : Not (((u + 1) % n) = v)) :
    Not
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          u) =
       GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          v)) := by
  intro hEq
  have hmemU := cycleCanonicalIncidentSupportKey_mem_even n u hn hu
  have hmemV :
      List.Mem (2 * u)
        (GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_cycle_derived n hn))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_cycle_derived n hn))
            v)) := by
    simpa [hEq] using hmemU
  exact cycleCanonicalIncidentSupportKey_not_mem_even_of_not_endpoint
    n u v hn hu hnotLeft hnotRight hmemV

/--
Symmetric key-separation form: if `u` is not an endpoint of cycle edge `v`,
then edge index `2*v` separates the keys for `u` and `v`.
-/
theorem cycleCanonicalIncidentSupportKeys_ne_of_right_not_endpoint
    (n u v : Nat) (hn : 1 < n) (hv : v < n)
    (hnotLeft : Not (v = u))
    (hnotRight : Not (((v + 1) % n) = u)) :
    Not
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          u) =
       GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          v)) := by
  intro hEq
  have hmemV := cycleCanonicalIncidentSupportKey_mem_even n v hn hv
  have hmemU :
      List.Mem (2 * v)
        (GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_cycle_derived n hn))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_cycle_derived n hn))
            u)) := by
    simpa [hEq] using hmemV
  exact cycleCanonicalIncidentSupportKey_not_mem_even_of_not_endpoint
    n v u hn hv hnotLeft hnotRight hmemU

/-- In a nontrivial cycle, one successor step never returns to the same vertex. -/
theorem cycle_successor_mod_ne_self
    (n u : Nat) (hn : 1 < n) (hu : u < n) :
    Not (((u + 1) % n) = u) := by
  intro h
  by_cases hnext : u + 1 < n
  case pos =>
    have hmod : (u + 1) % n = u + 1 := Nat.mod_eq_of_lt hnext
    rw [hmod] at h
    omega
  case neg =>
    have hle : u + 1 <= n := Nat.succ_le_of_lt hu
    have hge : n <= u + 1 := Nat.le_of_not_gt hnext
    have heq : u + 1 = n := Nat.le_antisymm hle hge
    have hmod : (u + 1) % n = 0 := by
      rw [heq]
      exact Nat.mod_self n
    rw [hmod] at h
    omega

/-- In a cycle of length at least three, two successor steps never return. -/
theorem cycle_successor_successor_mod_ne_self
    (n u : Nat) (hn : 2 < n) (hu : u < n) :
    Not ((((u + 1) % n + 1) % n) = u) := by
  intro h
  by_cases hnext : u + 1 < n
  case pos =>
    have hsucc1 : (u + 1) % n = u + 1 := Nat.mod_eq_of_lt hnext
    rw [hsucc1] at h
    by_cases hnext2 : u + 2 < n
    case pos =>
      have hsucc2 : (u + 2) % n = u + 2 := Nat.mod_eq_of_lt hnext2
      rw [show u + 1 + 1 = u + 2 by omega] at h
      rw [hsucc2] at h
      omega
    case neg =>
      have hle : u + 2 <= n := by
        omega
      have hge : n <= u + 2 := Nat.le_of_not_gt hnext2
      have heq : u + 2 = n := Nat.le_antisymm hle hge
      have hz : (u + 2) % n = 0 := by
        rw [heq]
        exact Nat.mod_self n
      rw [show u + 1 + 1 = u + 2 by omega] at h
      rw [hz] at h
      omega
  case neg =>
    have hle : u + 1 <= n := Nat.succ_le_of_lt hu
    have hge : n <= u + 1 := Nat.le_of_not_gt hnext
    have heq : u + 1 = n := Nat.le_antisymm hle hge
    have hsucc1 : (u + 1) % n = 0 := by
      rw [heq]
      exact Nat.mod_self n
    rw [hsucc1] at h
    have h1lt : 1 < n := by
      omega
    have hmod : (0 + 1) % n = 1 := Nat.mod_eq_of_lt h1lt
    rw [hmod] at h
    omega

/-- In a `circulant12` graph, one-step and two-step successors are distinct. -/
theorem circulant12_succ_two_mod_ne_succ
    (n u : Nat) (hn : 2 < n) :
    Not (((u + 2) % n) = ((u + 1) % n)) := by
  intro h
  have hsucc : (((u + 1) % n + 1) % n) = ((u + 2) % n) := by
    simp [Nat.mod_add_mod, Nat.add_assoc]
  have hne := TseitinModel.cycle_succ_mod_ne_self n ((u + 1) % n) (by omega)
    (Nat.mod_lt _ (by omega))
  apply hne
  rw [hsucc]
  exact h

/-- Adjacent successor vertices have distinct canonical incident-support keys for `n > 2`. -/
theorem cycleCanonicalIncidentSupportKeys_ne_of_successor
    (n u : Nat) (hn : 1 < n) (hn2 : 2 < n) (hu : u < n) :
    Not
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          u) =
       GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          ((u + 1) % n))) := by
  have hv : (u + 1) % n < n := Nat.mod_lt _ (by omega)
  exact cycleCanonicalIncidentSupportKeys_ne_of_right_not_endpoint
    n u ((u + 1) % n) hn hv
    (by
      exact cycle_successor_mod_ne_self n u hn hu)
    (by
      exact cycle_successor_successor_mod_ne_self n u hn2 hu)

/--
Nondegenerate derived-cycle vertex constraints have distinct canonical
incident-support keys whenever the vertices are distinct.
-/
theorem cycleCanonicalIncidentSupportKeys_ne_of_ne
    (n u v : Nat) (hn : 1 < n) (hn2 : 2 < n) (hu : u < n)
    (huv : Not (u = v)) :
    Not
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          u) =
       GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_cycle_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_cycle_derived n hn))
          v)) := by
  by_cases hsucc : ((u + 1) % n = v)
  case pos =>
    subst v
    exact cycleCanonicalIncidentSupportKeys_ne_of_successor n u hn hn2 hu
  case neg =>
    exact cycleCanonicalIncidentSupportKeys_ne_of_not_endpoint n u v hn hu huv hsucc

/--
`circulant12` vertex constraints have distinct canonical incident-support keys
whenever the vertices are distinct.
-/
theorem circulant12CanonicalIncidentSupportKeys_ne_of_ne
    (n u v : Nat) (hn : 2 < n) (hu : u < n)
    (huv : Not (u = v)) :
    Not
      (GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_circulant12_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_circulant12_derived n hn))
          u) =
       GroupFrame.canonicalSupportKeyForVars
        (incidentIndices
          (TseitinModel.GraphEncodingData.toGraph
            (TseitinModel.encoding_circulant12_derived n hn))
          (TseitinModel.m_eq_edges_length_of_encoding
            (TseitinModel.encoding_circulant12_derived n hn))
          v)) := by
  by_cases hsucc : ((u + 1) % n = v)
  case pos =>
    subst v
    intro hEq
    have hmemU := circulant12CanonicalIncidentSupportKey_mem_forwardTwo n u hn hu
    have hmemV :
        List.Mem (4 * u + 2)
          (GroupFrame.canonicalSupportKeyForVars
            (incidentIndices
              (TseitinModel.GraphEncodingData.toGraph
                (TseitinModel.encoding_circulant12_derived n hn))
              (TseitinModel.m_eq_edges_length_of_encoding
                (TseitinModel.encoding_circulant12_derived n hn))
              ((u + 1) % n))) := by
      simpa [hEq] using hmemU
    exact circulant12CanonicalIncidentSupportKey_not_mem_forwardTwo_of_not_endpoint
      n u ((u + 1) % n) hn hu
      (by
        intro h
        exact cycle_successor_mod_ne_self n u (by omega) hu h.symm)
      (circulant12_succ_two_mod_ne_succ n u hn)
      hmemV
  case neg =>
    intro hEq
    have hmemU := circulant12CanonicalIncidentSupportKey_mem_forwardOne n u hn hu
    have hmemV :
        List.Mem (4 * u)
          (GroupFrame.canonicalSupportKeyForVars
            (incidentIndices
              (TseitinModel.GraphEncodingData.toGraph
                (TseitinModel.encoding_circulant12_derived n hn))
              (TseitinModel.m_eq_edges_length_of_encoding
                (TseitinModel.encoding_circulant12_derived n hn))
              v)) := by
      simpa [hEq] using hmemU
    exact circulant12CanonicalIncidentSupportKey_not_mem_forwardOne_of_not_endpoint
      n u v hn hu huv hsucc hmemV

/--
Boundary fact for the current key-fresh cycle lane: in the two-vertex derived
cycle, both vertex constraints have the same canonical incident-support key.
-/
theorem twoCycleCanonicalIncidentSupportKeys_eq :
    GroupFrame.canonicalSupportKeyForVars
      (incidentIndices
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived 2 (by decide)))
        (TseitinModel.m_eq_edges_length_of_encoding
          (TseitinModel.encoding_cycle_derived 2 (by decide)))
        0) =
    GroupFrame.canonicalSupportKeyForVars
      (incidentIndices
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived 2 (by decide)))
        (TseitinModel.m_eq_edges_length_of_encoding
          (TseitinModel.encoding_cycle_derived 2 (by decide)))
        1) := by
  decide

/--
The `n = 2` derived cycle cannot satisfy the second snoc-step freshness premise
for the current `GeneratedCanonicalKeyFreshSpecList` lane: appending vertex `1`
after vertex `0` would require distinct canonical support keys, but the keys are
equal.
-/
theorem twoCycleSecondVertexFreshnessStep_false :
    Not
      (let G := TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived 2 (by decide))
       let hme := TseitinModel.m_eq_edges_length_of_encoding
          (TseitinModel.encoding_cycle_derived 2 (by decide))
       forall spec : GeneratedParitySpec G.m,
        List.Mem spec
          (generatedParitySpecsFromIncident [0] (incidentIndices G hme)
            cycleRootCharge) ->
          Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme 1) =
            GroupFrame.canonicalSupportKeyForVars spec.1)) := by
  intro hfresh
  dsimp at hfresh
  let G := TseitinModel.GraphEncodingData.toGraph
    (TseitinModel.encoding_cycle_derived 2 (by decide))
  let hme := TseitinModel.m_eq_edges_length_of_encoding
    (TseitinModel.encoding_cycle_derived 2 (by decide))
  have hmem :
      List.Mem
        (incidentIndices G hme 0, cycleRootCharge 0)
        (generatedParitySpecsFromIncident [0] (incidentIndices G hme)
          cycleRootCharge) := by
    change List.Mem
      (incidentIndices G hme 0, cycleRootCharge 0)
      [(incidentIndices G hme 0, cycleRootCharge 0)]
    exact List.Mem.head []
  exact hfresh (incidentIndices G hme 0, cycleRootCharge 0) hmem
    (by
      change GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_cycle_derived 2 (by decide)))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_cycle_derived 2 (by decide)))
            1) =
        GroupFrame.canonicalSupportKeyForVars
          (incidentIndices
            (TseitinModel.GraphEncodingData.toGraph
              (TseitinModel.encoding_cycle_derived 2 (by decide)))
            (TseitinModel.m_eq_edges_length_of_encoding
              (TseitinModel.encoding_cycle_derived 2 (by decide)))
            0)
      exact twoCycleCanonicalIncidentSupportKeys_eq.symm)

/--
Executable boundary for the current support-key splitter on the two-cycle:
the merged same-support component is not recognized as any parity block.
-/
theorem twoCycleCanonicalSplitterBlocks_length :
    (splitArityFourParityCanonicalSupportGroups
      (TseitinCycleCNFFormula 2 (by decide))).blocks.length = 0 := by
  decide

/--
Executable boundary for the current support-key splitter on the two-cycle:
all generated clauses remain residual.
-/
theorem twoCycleCanonicalSplitterResidualCNF_length :
    (splitArityFourParityCanonicalSupportGroups
      (TseitinCycleCNFFormula 2 (by decide))).residualCNF.length = 16 := by
  decide

/-- The current splitter emits no covered core CNF on the two-cycle. -/
theorem twoCycleCanonicalSplitterCoreCNF_eq :
    (splitArityFourParityCanonicalSupportGroups
      (TseitinCycleCNFFormula 2 (by decide))).coreCNF = [] := by
  decide

/-- The current splitter's expanded CNF is exactly the residual two-cycle CNF. -/
theorem twoCycleCanonicalSplitterExpandedCNF_eq :
    (splitArityFourParityCanonicalSupportGroups
      (TseitinCycleCNFFormula 2 (by decide))).expandedCNF =
      TseitinCycleCNFFormula 2 (by decide) := by
  decide

/-- The current splitter leaves the entire two-cycle CNF residual. -/
theorem twoCycleCanonicalSplitterResidualCNF_eq :
    (splitArityFourParityCanonicalSupportGroups
      (TseitinCycleCNFFormula 2 (by decide))).residualCNF =
      TseitinCycleCNFFormula 2 (by decide) := by
  decide

/--
The current executable extractor is not residual-free for the direct
two-equation GF(2) target of the two-cycle.  This separates the already-proved
semantic class membership for `1 < n` from current executable recognition at
the same-support `n = 2` boundary.
-/
theorem twoCycleCanonicalSplitter_not_residualFree_for_directGF2 :
    Not
      (ExtractorCompleteness.ExtractorCompleteOn
        (TseitinCycleCNFFormula 2 (by decide))
        (TseitinParityFormulaFromEncoding
          (TseitinModel.encoding_cycle_derived 2 (by decide))
          cycleRootCharge)) := by
  intro h
  cases h with
  | intro blocks hrest =>
      cases hrest with
      | intro hsplit _hperm =>
          have hzero :
              (splitArityFourParityCanonicalSupportGroups
                (TseitinCycleCNFFormula 2 (by decide))).residualCNF.length = 0 := by
            rw [hsplit]
            rfl
          have hsixteen :
              (splitArityFourParityCanonicalSupportGroups
                (TseitinCycleCNFFormula 2 (by decide))).residualCNF.length = 16 :=
            twoCycleCanonicalSplitterResidualCNF_length
          omega

/--
Snoc-order side-condition package for finite generated parity spec lists.
Each appended spec must be nonempty, in canonical support order, and
support-disjoint from the accumulated prefix.
-/
inductive GeneratedSupportDisjointSpecList (m : Nat) :
    List (GeneratedParitySpec m) -> Prop
  | empty :
      GeneratedSupportDisjointSpecList m []
  | snoc
      {specs : List (GeneratedParitySpec m)}
      {vars : List (Fin m)}
      {charge : Bool}
      {c : CNFModel.Clause m}
      {tail : CNFModel.CNF m}
      (hprefix : GeneratedSupportDisjointSpecList m specs)
      (hdisjoint :
        ParityEncoded.DisjointSupport
          (generatedParitySpecsCNF specs)
          (clausesForVertex vars charge))
      (hcnf : clausesForVertex vars charge = c :: tail)
      (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
      (hvars : Not (vars = [])) :
      GeneratedSupportDisjointSpecList m (specs ++ [(vars, charge)])

/--
The generated-spec list side-condition package instantiates the lower-level
finite support-disjoint family class used by the executable extractor theorem.
-/
theorem generatedSupportDisjointFamily_of_specList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedSupportDisjointSpecList m specs) :
    GeneratedSupportDisjointFamily m
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) := by
  induction hspecs with
  | empty =>
      exact GeneratedSupportDisjointFamily.empty
  | snoc _hprefix hdisjoint hcnf hnormal hvars ih =>
      rename_i specs vars charge _c _tail
      rw [generatedParitySpecsCNF_append_singleton,
        generatedParitySpecsGF2_append_singleton]
      exact
        GeneratedSupportDisjointFamily.snoc
          ih hdisjoint hcnf hnormal hvars

/--
Every generated support-disjoint spec list has a recognized canonical support
group decomposition whose compact GF(2) output matches the folded spec output
up to permutation.
-/
theorem groupsRecognized_exists_of_generatedSupportDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedSupportDisjointSpecList m specs) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport (generatedParitySpecsCNF specs))
        blocks /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 blocks)
          (generatedParitySpecsGF2 specs) :=
  groupsRecognized_exists_of_generatedSupportDisjointFamily
    (generatedSupportDisjointFamily_of_specList hspecs)

/--
Generated support-disjoint spec lists are residual-free for the executable
canonical extractor, with the folded GF(2) spec formula as output.
-/
theorem extractorCompleteOn_of_generatedSupportDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedSupportDisjointSpecList m specs) :
    ExtractorCompleteness.ExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  extractorCompleteOn_of_generatedSupportDisjointFamily
    (generatedSupportDisjointFamily_of_specList hspecs)

/--
Snoc-order side-condition package for finite generated parity spec lists whose
new blocks have fresh canonical support keys relative to the accumulated prefix.
-/
inductive GeneratedKeyDisjointSpecList (m : Nat) :
    List (GeneratedParitySpec m) -> Prop
  | empty :
      GeneratedKeyDisjointSpecList m []
  | snoc
      {specs : List (GeneratedParitySpec m)}
      {vars : List (Fin m)}
      {charge : Bool}
      {c : CNFModel.Clause m}
      {tail : CNFModel.CNF m}
      (hprefix : GeneratedKeyDisjointSpecList m specs)
      (hkeyDisjoint :
        GroupFrame.CNFClauseKeysDisjoint
          (generatedParitySpecsCNF specs)
          (clausesForVertex vars charge))
      (hcnf : clausesForVertex vars charge = c :: tail)
      (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
      GeneratedKeyDisjointSpecList m (specs ++ [(vars, charge)])

/--
Spec-level side-condition package for generated parity lists.  Each appended
spec must have a canonical support key fresh for every earlier spec.  This is a
caller-facing form of the clause-level `GeneratedKeyDisjointSpecList` condition.
-/
inductive GeneratedCanonicalKeyFreshSpecList (m : Nat) :
    List (GeneratedParitySpec m) -> Prop
  | empty :
      GeneratedCanonicalKeyFreshSpecList m []
  | snoc
      {specs : List (GeneratedParitySpec m)}
      {vars : List (Fin m)}
      {charge : Bool}
      {c : CNFModel.Clause m}
      {tail : CNFModel.CNF m}
      (hprefix : GeneratedCanonicalKeyFreshSpecList m specs)
      (hfresh :
        forall spec : GeneratedParitySpec m,
          List.Mem spec specs ->
            Not (GroupFrame.canonicalSupportKeyForVars vars =
              GroupFrame.canonicalSupportKeyForVars spec.1))
      (hcnf : clausesForVertex vars charge = c :: tail)
      (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
      GeneratedCanonicalKeyFreshSpecList m (specs ++ [(vars, charge)])

/--
Caller-facing constructor for canonical-key-fresh generated spec lists.  This
lets graph-family proofs provide the nonempty CNF side condition as an
existential witness instead of naming the head clause and tail explicitly.
-/
theorem generatedCanonicalKeyFreshSpecList_snoc_of_exists
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    {vars : List (Fin m)}
    {charge : Bool}
    (hprefix : GeneratedCanonicalKeyFreshSpecList m specs)
    (hfresh :
      forall spec : GeneratedParitySpec m,
        List.Mem spec specs ->
          Not (GroupFrame.canonicalSupportKeyForVars vars =
            GroupFrame.canonicalSupportKeyForVars spec.1))
    (hcnf :
      exists c : CNFModel.Clause m,
        exists tail : CNFModel.CNF m,
          clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    GeneratedCanonicalKeyFreshSpecList m (specs ++ [(vars, charge)]) := by
  rcases hcnf with ⟨c, tail, hcnf⟩
  exact GeneratedCanonicalKeyFreshSpecList.snoc hprefix hfresh hcnf hnormal

/--
Snoc step for incident-generated spec lists.  This is the reusable induction
step needed by graph-family certificates: a prefix certificate extends when the
new vertex's canonical support key is fresh against all earlier generated
vertices and the new generated block is nonempty and in canonical support order.
-/
theorem generatedCanonicalKeyFreshSpecList_fromIncident_append_singleton
    {m : Nat}
    {vertices : List Nat}
    {v : Nat}
    {incident : Nat -> List (Fin m)}
    {charge : Nat -> Bool}
    (hprefix :
      GeneratedCanonicalKeyFreshSpecList m
        (generatedParitySpecsFromIncident vertices incident charge))
    (hfresh :
      forall prior : Nat,
        List.Mem prior vertices ->
          Not (GroupFrame.canonicalSupportKeyForVars (incident v) =
            GroupFrame.canonicalSupportKeyForVars (incident prior)))
    (hcnf :
      exists c : CNFModel.Clause m,
        exists tail : CNFModel.CNF m,
          clausesForVertex (incident v) (charge v) = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder (incident v)) :
    GeneratedCanonicalKeyFreshSpecList m
      (generatedParitySpecsFromIncident (vertices ++ [v]) incident charge) := by
  rw [generatedParitySpecsFromIncident_append_singleton]
  apply generatedCanonicalKeyFreshSpecList_snoc_of_exists hprefix ?_ hcnf hnormal
  intro spec hspec
  unfold generatedParitySpecsFromIncident at hspec
  rcases List.mem_map.1 hspec with ⟨prior, hprior, hspec_eq⟩
  subst spec
  exact hfresh prior hprior

/--
Generic range-prefix certificate for incident-generated graph encodings.  If
each newly appended vertex has a canonical incident-support key fresh against
all earlier vertices, and every generated vertex block is nonempty, then the
folded generated-spec list carries the canonical-key freshness certificate.
-/
theorem generatedCanonicalKeyFreshSpecList_fromIncident_range_prefix
    (G : TseitinModel.Graph)
    (hme : G.m = G.edges.length)
    (charge : Nat -> Bool)
    (k : Nat)
    (hfresh :
      forall v prior : Nat,
        v < k ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hcnf :
      forall v : Nat,
        v < k ->
          exists c : CNFModel.Clause G.m,
            exists tail : CNFModel.CNF G.m,
              clausesForVertex (incidentIndices G hme v) (charge v) = c :: tail) :
    GeneratedCanonicalKeyFreshSpecList G.m
      (generatedParitySpecsFromIncident (List.range k) (incidentIndices G hme)
        charge) := by
  induction k with
  | zero =>
      dsimp [generatedParitySpecsFromIncident]
      exact GeneratedCanonicalKeyFreshSpecList.empty
  | succ k ih =>
      rw [List.range_succ]
      exact generatedCanonicalKeyFreshSpecList_fromIncident_append_singleton
        (hprefix :=
          ih
            (fun v prior hv hprior => hfresh v prior (by omega) hprior)
            (fun v hv => hcnf v (by omega)))
        (hfresh :=
          fun prior hprior =>
            let hpriorLt : prior < k := List.mem_range.1 hprior
            hfresh k prior (by omega) hpriorLt)
        (hcnf := hcnf k (by omega))
        (hnormal := incidentIndices_varsInCanonicalSupportOrder G hme k)

/--
Concrete graph encodings obtain the generated-spec freshness certificate from
pairwise fresh incident-support keys and per-vertex nonempty generated blocks.
-/
theorem generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hcnf :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v : Nat,
        v < G.n ->
          exists c : CNFModel.Clause G.m,
            exists tail : CNFModel.CNF G.m,
              clausesForVertex (incidentIndices G hme v) (charge v) = c :: tail) :
    GeneratedCanonicalKeyFreshSpecList
      (TseitinModel.GraphEncodingData.toGraph enc).m
      (generatedParitySpecsFromEncoding enc charge) := by
  dsimp [generatedParitySpecsFromEncoding]
  exact generatedCanonicalKeyFreshSpecList_fromIncident_range_prefix
    (TseitinModel.GraphEncodingData.toGraph enc)
    (TseitinModel.m_eq_edges_length_of_encoding enc)
    charge
    (TseitinModel.GraphEncodingData.toGraph enc).n
    hfresh
    hcnf

/--
Concrete graph encodings obtain the generated-spec freshness certificate from
pairwise fresh incident-support keys and a positive-degree condition at every
vertex.  Positive degree is enough because any nonempty incident-variable list
expands to at least one ordinary parity CNF clause.
-/
theorem generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat,
        v < G.n -> 0 < TseitinModel.degree G v) :
    GeneratedCanonicalKeyFreshSpecList
      (TseitinModel.GraphEncodingData.toGraph enc).m
      (generatedParitySpecsFromEncoding enc charge) := by
  let G := TseitinModel.GraphEncodingData.toGraph enc
  let hme := TseitinModel.m_eq_edges_length_of_encoding enc
  have hcnf :
      forall v : Nat,
        v < G.n ->
          exists c : CNFModel.Clause G.m,
            exists tail : CNFModel.CNF G.m,
              clausesForVertex (incidentIndices G hme v) (charge v) = c :: tail := by
    intro v hv
    exact incidentClausesForVertex_exists_cons_of_degree_pos
      G hme v (charge v) (hdegree v hv)
  exact generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh
    enc charge hfresh hcnf

/--
Prefix certificate for the nondegenerate derived cycle family.  The induction
adds vertices in range order; the fresh-key side condition is discharged by the
cycle-specific pairwise incident-support-key theorem.
-/
theorem generatedCanonicalKeyFreshSpecList_forCycle_prefix
    (n k : Nat) (hn : 1 < n) (hn2 : 2 < n) (hk : k <= n) :
    let G := TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived n hn)
    let hme := TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_cycle_derived n hn)
    GeneratedCanonicalKeyFreshSpecList G.m
      (generatedParitySpecsFromIncident (List.range k) (incidentIndices G hme)
        cycleRootCharge) := by
  induction k with
  | zero =>
      dsimp [generatedParitySpecsFromIncident]
      exact GeneratedCanonicalKeyFreshSpecList.empty
  | succ k ih =>
      have hkPrefix : k <= n := by omega
      have hkLt : k < n := by omega
      dsimp
      rw [List.range_succ]
      apply generatedCanonicalKeyFreshSpecList_fromIncident_append_singleton
      case hprefix =>
        simpa using ih hkPrefix
      case hfresh =>
        intro prior hprior
        have hpriorLt : prior < k := List.mem_range.1 hprior
        simpa using
          cycleCanonicalIncidentSupportKeys_ne_of_ne n k prior hn hn2 hkLt (by omega)
      case hcnf =>
        simpa using cycleClausesForVertex_exists_cons n k hn hkLt
      case hnormal =>
        simpa using cycleIncidentIndices_varsInCanonicalSupportOrder n k hn

/--
The generated incident specs for every nondegenerate derived cycle satisfy the
spec-level canonical-key freshness certificate expected by the executable
extractor theorem package.
-/
theorem generatedCanonicalKeyFreshSpecList_forCycle
    (n : Nat) (hn : 1 < n) (hn2 : 2 < n) :
    GeneratedCanonicalKeyFreshSpecList
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m
      (generatedParitySpecsForCycle n hn) := by
  simpa [generatedParitySpecsForCycle, generatedParitySpecsFromEncoding] using
    generatedCanonicalKeyFreshSpecList_forCycle_prefix n n hn hn2 (Nat.le_refl n)

/--
Freshness of generated spec support keys supplies the clause-level key-disjoint
side condition expected by the executable extractor theorem package.
-/
theorem generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    GeneratedKeyDisjointSpecList m specs := by
  induction hspecs with
  | empty =>
      exact GeneratedKeyDisjointSpecList.empty
  | snoc _hprefix hfresh hcnf hnormal ih =>
      exact
        GeneratedKeyDisjointSpecList.snoc
          ih
          (clauseKeysDisjoint_generatedParitySpecsCNF_of_freshCanonicalSupportKeys
            hfresh)
          hcnf
          hnormal

/--
The generated key-disjoint spec-list side-condition package instantiates the
lower-level finite key-disjoint family class used by the executable extractor
theorem.
-/
theorem generatedKeyDisjointFamily_of_specList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    GeneratedKeyDisjointFamily m
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) := by
  induction hspecs with
  | empty =>
      exact GeneratedKeyDisjointFamily.empty
  | snoc _hprefix hkeyDisjoint hcnf hnormal ih =>
      rename_i specs vars charge _c _tail
      rw [generatedParitySpecsCNF_append_singleton,
        generatedParitySpecsGF2_append_singleton]
      exact
        GeneratedKeyDisjointFamily.snoc
          ih hkeyDisjoint hcnf hnormal

/--
Generated key-disjoint spec lists produce declarative parity-encoded class
witnesses for their folded CNF/GF(2) expansions.
-/
theorem class_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    ParityEncoded.Class m
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  class_of_generatedKeyDisjointFamily
    (generatedKeyDisjointFamily_of_specList hspecs)

/--
Fresh canonical support keys are enough to obtain a declarative parity-encoded
class witness for the folded generated spec list.
-/
theorem class_of_generatedCanonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    ParityEncoded.Class m
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  class_of_generatedKeyDisjointSpecList
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Every generated key-disjoint spec list has a recognized canonical support-group
decomposition whose compact GF(2) output matches the folded spec output up to
permutation.
-/
theorem groupsRecognized_exists_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport (generatedParitySpecsCNF specs))
        blocks /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 blocks)
          (generatedParitySpecsGF2 specs) :=
  groupsRecognized_exists_of_generatedKeyDisjointFamily
    (generatedKeyDisjointFamily_of_specList hspecs)

/--
Generated key-disjoint spec lists are residual-free for the executable canonical
extractor, with the folded GF(2) spec formula as output.
-/
theorem extractorCompleteOn_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    ExtractorCompleteness.ExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  extractorCompleteOn_of_generatedKeyDisjointFamily
    (generatedKeyDisjointFamily_of_specList hspecs)

/--
Generated spec lists with fresh canonical support keys are residual-free for
the executable canonical extractor.
-/
theorem extractorCompleteOn_of_generatedCanonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    ExtractorCompleteness.ExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  extractorCompleteOn_of_generatedKeyDisjointSpecList
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Generated key-disjoint spec lists satisfy the combined semantic/executable
extraction claim for their folded CNF/GF(2) expansions.
-/
theorem semanticExtractorCompleteOn_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  ExtractorCompleteness.semanticExtractorCompleteOn_of_class
    (class_of_generatedKeyDisjointSpecList hspecs)
    (extractorCompleteOn_of_generatedKeyDisjointSpecList hspecs)

/--
Generated spec lists with fresh canonical support keys satisfy the combined
semantic/executable extraction claim.
-/
theorem semanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  semanticExtractorCompleteOn_of_generatedKeyDisjointSpecList
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Every concrete graph encoding generated by the Tseitin encoder is in the
declarative parity-encoded class.  This is the semantic-only lane: it carries no
key-freshness, nonempty-block, or extractor-completeness premise.
-/
theorem class_of_tseitinCNFFormulaFromEncoding
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph enc).m
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  rw [(generatedParitySpecsCNF_fromEncoding enc charge).symm,
    (generatedParitySpecsGF2_fromEncoding enc charge).symm]
  exact class_of_generatedParitySpecs
    (generatedParitySpecsFromEncoding enc charge)

/--
If a concrete graph encoding's generated incident specs satisfy the accumulated
key-disjoint side condition, the ordinary Tseitin CNF and its compact GF(2)
formula are in the declarative parity-encoded class.
-/
theorem class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph enc).m
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  rw [← generatedParitySpecsCNF_fromEncoding enc charge,
    ← generatedParitySpecsGF2_fromEncoding enc charge]
  exact class_of_generatedKeyDisjointSpecList hspecs

/--
Concrete graph encodings with fresh canonical support keys obtain a declarative
parity-encoded class witness for their ordinary Tseitin CNF/GF(2) pair.
-/
theorem class_of_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph enc).m
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    enc charge (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Concrete graph encodings are in the declarative parity-encoded class whenever
their incident-generated vertex blocks are nonempty and their canonical
incident-support keys are fresh in vertex-range order.
-/
theorem class_of_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hcnf :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v : Nat,
        v < G.n ->
          exists c : CNFModel.Clause G.m,
            exists tail : CNFModel.CNF G.m,
              clausesForVertex (incidentIndices G hme v) (charge v) = c :: tail) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph enc).m
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  class_of_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh
      enc charge hfresh hcnf)

/--
Concrete graph encodings are in the declarative parity-encoded class whenever
every vertex has positive degree and the canonical incident-support keys are
fresh in vertex-range order.
-/
theorem class_of_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat,
        v < G.n -> 0 < TseitinModel.degree G v) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph enc).m
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  class_of_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos
      enc charge hfresh hdegree)

/--
If a concrete graph encoding's generated incident specs satisfy the accumulated
key-disjoint side condition, the existing Tseitin CNF encoder is residual-free
for the executable canonical splitter.
-/
theorem extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  rw [← generatedParitySpecsCNF_fromEncoding enc charge,
    ← generatedParitySpecsGF2_fromEncoding enc charge]
  exact extractorCompleteOn_of_generatedKeyDisjointSpecList hspecs

/--
Concrete graph encodings are residual-free when their generated incident specs
carry the spec-level canonical-key freshness certificate.
-/
theorem extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    enc charge (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Concrete graph encodings are residual-free for the executable canonical
support splitter whenever their incident-generated vertex blocks are nonempty
and their canonical incident-support keys are fresh in vertex-range order.
-/
theorem extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hcnf :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v : Nat,
        v < G.n ->
          exists c : CNFModel.Clause G.m,
            exists tail : CNFModel.CNF G.m,
              clausesForVertex (incidentIndices G hme v) (charge v) = c :: tail) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh
      enc charge hfresh hcnf)

/--
Concrete graph encodings are residual-free for the executable canonical
support splitter whenever every vertex has positive degree and the canonical
incident-support keys are fresh in vertex-range order.
-/
theorem extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat,
        v < G.n -> 0 < TseitinModel.degree G v) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos
      enc charge hfresh hdegree)

/--
Concrete graph encodings whose generated incident specs satisfy accumulated
key-disjointness satisfy the combined semantic/executable extraction claim.
-/
theorem semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  ExtractorCompleteness.semanticExtractorCompleteOn_of_class
    (class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
      enc charge hspecs)
    (extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
      enc charge hspecs)

/--
Concrete graph encodings whose generated incident specs satisfy spec-level
canonical-key freshness satisfy the combined semantic/executable extraction
claim.
-/
theorem semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    enc charge (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Concrete graph encodings with nonempty generated vertex blocks and fresh
canonical incident-support keys satisfy the combined semantic/executable
extraction claim.
-/
theorem semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hcnf :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v : Nat,
        v < G.n ->
          exists c : CNFModel.Clause G.m,
            exists tail : CNFModel.CNF G.m,
              clausesForVertex (incidentIndices G hme v) (charge v) = c :: tail) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh
      enc charge hfresh hcnf)

/--
Concrete graph encodings with positive vertex degree and fresh canonical
incident-support keys satisfy the combined semantic/executable extraction claim.
-/
theorem semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat,
        v < G.n -> 0 < TseitinModel.degree G v) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos
      enc charge hfresh hdegree)

/--
The derived `circulant12` graph family is residual-free for the executable
canonical support splitter once its canonical incident-support keys are fresh.
The positive-degree side condition is discharged by the graph-family degree
theorem, so the remaining obligation is exactly the fresh-key analysis.
-/
theorem extractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool)
    (hfresh :
      let enc := TseitinModel.encoding_circulant12_derived n hn
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior))) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) := by
  let enc := TseitinModel.encoding_circulant12_derived n hn
  have hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat, v < G.n -> 0 < TseitinModel.degree G v := by
    dsimp [enc]
    intro v hv
    exact TseitinModel.circulant12_degree_pos n v hn hv
  exact extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos
    enc charge hfresh hdegree

/--
The derived `circulant12` graph family is in the declarative parity-encoded
class once its canonical incident-support keys are fresh.
-/
theorem class_of_TseitinCirculant12CNFFormula_of_incidentKeyFresh
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool)
    (hfresh :
      let enc := TseitinModel.encoding_circulant12_derived n hn
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior))) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_circulant12_derived n hn)).m
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) := by
  let enc := TseitinModel.encoding_circulant12_derived n hn
  have hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat, v < G.n -> 0 < TseitinModel.degree G v := by
    dsimp [enc]
    intro v hv
    exact TseitinModel.circulant12_degree_pos n v hn hv
  exact class_of_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos
    enc charge hfresh hdegree

/--
The derived `circulant12` graph family satisfies the combined
semantic/executable extraction claim once its canonical incident-support keys
are fresh.
-/
theorem semanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool)
    (hfresh :
      let enc := TseitinModel.encoding_circulant12_derived n hn
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior))) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) :=
  ExtractorCompleteness.semanticExtractorCompleteOn_of_class
    (class_of_TseitinCirculant12CNFFormula_of_incidentKeyFresh
      n hn charge hfresh)
    (extractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh
      n hn charge hfresh)

/--
The derived `circulant12` family has fresh canonical incident-support keys in
vertex order.  The proof separates two distinct vertices by either the
forward-one edge slot `4*u` or, for the immediate successor case, the
forward-two edge slot `4*u + 2`.
-/
theorem circulant12IncidentSupportKeys_fresh
    (n : Nat) (hn : 2 < n) :
    let enc := TseitinModel.encoding_circulant12_derived n hn
    let G := TseitinModel.GraphEncodingData.toGraph enc
    let hme := TseitinModel.m_eq_edges_length_of_encoding enc
    forall v prior : Nat,
      v < G.n ->
        prior < v ->
          Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
            GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
  dsimp
  intro v prior hv hprior
  have hvn : v < n := by
    simpa [TseitinModel.encoding_circulant12_derived,
      TseitinModel.GraphEncodingData.toGraph] using hv
  exact circulant12CanonicalIncidentSupportKeys_ne_of_ne n v prior hn hvn (by omega)

/--
The derived `circulant12` graph family is residual-free for the executable
canonical support splitter.
-/
theorem extractorCompleteOn_TseitinCirculant12CNFFormula
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) :=
  extractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh
    n hn charge (circulant12IncidentSupportKeys_fresh n hn)

/--
The derived `circulant12` graph family is in the declarative parity-encoded
class.
-/
theorem class_of_TseitinCirculant12CNFFormula
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_circulant12_derived n hn)).m
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) :=
  class_of_TseitinCirculant12CNFFormula_of_incidentKeyFresh
    n hn charge (circulant12IncidentSupportKeys_fresh n hn)

/--
The derived `circulant12` graph family satisfies the combined
semantic/executable extraction claim.
-/
theorem semanticExtractorCompleteOn_TseitinCirculant12CNFFormula
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) :=
  semanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh
    n hn charge (circulant12IncidentSupportKeys_fresh n hn)

/--
Cycle-family class membership reduces to the concrete key-disjoint
side-condition for the generated incident-spec list.
-/
theorem class_of_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  dsimp [TseitinCycleCNFFormula, generatedParitySpecsForCycle]
  exact
    class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
      (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge hspecs

/--
Cycle-family class membership also reduces to the cleaner spec-level
canonical-key freshness certificate.
-/
theorem class_of_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  class_of_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    n hn (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Every derived cycle, including the two-vertex boundary, is in the declarative
parity-encoded class.  The `2 < n` hypothesis is only needed by the executable
fresh-key extractor lane, not by semantic generated-spec class membership.
-/
theorem class_of_TseitinCycleCNFFormula
    (n : Nat) (hn : 1 < n) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  dsimp [TseitinCycleCNFFormula]
  exact
    class_of_tseitinCNFFormulaFromEncoding
      (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge

/--
Every nondegenerate derived cycle is in the declarative parity-encoded class.
-/
theorem class_of_TseitinCycleCNFFormula_nonDegenerate
    (n : Nat) (hn : 1 < n) (hn2 : 2 < n) :
    ParityEncoded.Class
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  class_of_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    n hn (generatedCanonicalKeyFreshSpecList_forCycle n hn hn2)

/--
Cycle-family extractor completeness reduces to the concrete key-disjoint
side-condition for the generated incident-spec list.
-/
theorem extractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  dsimp [TseitinCycleCNFFormula, generatedParitySpecsForCycle]
  exact
    extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
      (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge hspecs

/--
Cycle-family extractor completeness also reduces to the cleaner spec-level
canonical-key freshness certificate.
-/
theorem extractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  extractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    n hn (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Nondegenerate derived cycles are residual-free for the executable canonical
support splitter.  The only excluded cycle-family case is the certified
two-vertex boundary where both generated vertex constraints share the same
canonical incident-support key.
-/
theorem extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate
    (n : Nat) (hn : 1 < n) (hn2 : 2 < n) :
    ExtractorCompleteness.ExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  extractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    n hn (generatedCanonicalKeyFreshSpecList_forCycle n hn hn2)

/--
Cycle-family combined semantic/executable extraction reduces to the concrete
key-disjoint side-condition for the generated incident-spec list.
-/
theorem semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  ExtractorCompleteness.semanticExtractorCompleteOn_of_class
    (class_of_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
      n hn hspecs)
    (extractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
      n hn hspecs)

/--
Cycle-family combined semantic/executable extraction also reduces to the
cleaner spec-level canonical-key freshness certificate.
-/
theorem semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    n hn (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Nondegenerate derived cycles satisfy the combined semantic/executable
extraction claim.
-/
theorem semanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate
    (n : Nat) (hn : 1 < n) (hn2 : 2 < n) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    n hn (generatedCanonicalKeyFreshSpecList_forCycle n hn hn2)

/-- Covered CNF for appended canonical block lists is covered-CNF append. -/
theorem canonicalFingerprintRecognizedBlocksCNF_append
    {m : Nat}
    (left right : List (CanonicalFingerprintRecognizedParityBlock m)) :
    canonicalFingerprintRecognizedBlocksCNF (left ++ right) =
      canonicalFingerprintRecognizedBlocksCNF left ++
        canonicalFingerprintRecognizedBlocksCNF right := by
  induction left with
  | nil => rfl
  | cons b left ih =>
      simp [canonicalFingerprintRecognizedBlocksCNF, ih]

/-- Disjointness from an appended CNF follows from disjointness from both sides. -/
theorem disjointSupport_append_right
    {m : Nat} {f g h : CNFModel.CNF m}
    (hfg : ParityEncoded.DisjointSupport f g)
    (hfh : ParityEncoded.DisjointSupport f h) :
    ParityEncoded.DisjointSupport f (g ++ h) := by
  intro v hv hmem
  unfold ParityEncoded.cnfSupport at hmem
  rw [List.bind_append] at hmem
  cases List.mem_append.1 hmem with
  | inl hg => exact hfg v hv hg
  | inr hh => exact hfh v hv hh

/-- CNF support membership transports backward across clause-list permutation. -/
theorem cnfSupport_mem_of_perm
    {m : Nat} {f g : CNFModel.CNF m}
    (hperm : List.Perm f g)
    {v : Fin m}
    (hv : List.Mem v (ParityEncoded.cnfSupport g)) :
    List.Mem v (ParityEncoded.cnfSupport f) := by
  unfold ParityEncoded.cnfSupport at hv
  unfold ParityEncoded.cnfSupport
  cases List.mem_bind.1 hv with
  | intro c hcAnd =>
      cases hcAnd with
      | intro hcg hvc =>
          exact List.mem_bind.2
            (Exists.intro c
              (And.intro (hperm.symm.subset hcg) hvc))

/-- CNF support disjointness is invariant under clause-list permutation. -/
theorem disjointSupport_of_perm
    {m : Nat} {f f' g g' : CNFModel.CNF m}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hf : List.Perm f' f)
    (hg : List.Perm g' g) :
    ParityEncoded.DisjointSupport f' g' := by
  intro v hvf hvg
  exact hdisjoint v
    (cnfSupport_mem_of_perm hf.symm hvf)
    (cnfSupport_mem_of_perm hg.symm hvg)

/-- Per-block literal-level permutation certificates for canonical blocks. -/
def CanonicalBlocksPermCertified {m : Nat} :
    List (CanonicalFingerprintRecognizedParityBlock m) -> Prop
  | [] => True
  | b :: blocks =>
      List.Perm b.blockCNF b.spec.expandedCNF /\
        CanonicalBlocksPermCertified blocks

/-- Permutation certificates compose over appended canonical block lists. -/
theorem CanonicalBlocksPermCertified.append
    {m : Nat}
    {left right : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hleft : CanonicalBlocksPermCertified left)
    (hright : CanonicalBlocksPermCertified right) :
    CanonicalBlocksPermCertified (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons _b _left ih =>
      exact And.intro hleft.1 (ih hleft.2)

/--
Append-oriented disjointness needed to build a `ParityEncoded.Class` by folding
canonical recognized blocks from left to right.
-/
def CanonicalBlocksAppendDisjoint {m : Nat} :
    List (CanonicalFingerprintRecognizedParityBlock m) -> Prop
  | [] => True
  | b :: blocks =>
      ParityEncoded.DisjointSupport
        b.blockCNF (canonicalFingerprintRecognizedBlocksCNF blocks) /\
        CanonicalBlocksAppendDisjoint blocks

/-- The empty canonical block list is append-disjoint. -/
theorem CanonicalBlocksAppendDisjoint.nil
    {m : Nat} :
    CanonicalBlocksAppendDisjoint ([] :
      List (CanonicalFingerprintRecognizedParityBlock m)) := by
  exact True.intro

/-- A singleton canonical block list is append-disjoint. -/
theorem CanonicalBlocksAppendDisjoint.singleton
    {m : Nat}
    (b : CanonicalFingerprintRecognizedParityBlock m) :
    CanonicalBlocksAppendDisjoint [b] := by
  constructor
  case left =>
    intro _v _hv hmem
    unfold canonicalFingerprintRecognizedBlocksCNF at hmem
    cases hmem
  case right =>
    exact CanonicalBlocksAppendDisjoint.nil

/-- Every block in a canonical list is support-disjoint from a target CNF. -/
def CanonicalBlocksDisjointFromCNF {m : Nat}
    (blocks : List (CanonicalFingerprintRecognizedParityBlock m))
    (f : CNFModel.CNF m) : Prop :=
  forall b : CanonicalFingerprintRecognizedParityBlock m,
    List.Mem b blocks -> ParityEncoded.DisjointSupport b.blockCNF f

/--
Append-disjointness composes when every left block is disjoint from the right
list's covered CNF.
-/
theorem CanonicalBlocksAppendDisjoint.append
    {m : Nat}
    {left right : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hleft : CanonicalBlocksAppendDisjoint left)
    (hright : CanonicalBlocksAppendDisjoint right)
    (hcross : CanonicalBlocksDisjointFromCNF left
      (canonicalFingerprintRecognizedBlocksCNF right)) :
    CanonicalBlocksAppendDisjoint (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons b left ih =>
      change ParityEncoded.DisjointSupport b.blockCNF
          (canonicalFingerprintRecognizedBlocksCNF (left ++ right)) /\
        CanonicalBlocksAppendDisjoint (left ++ right)
      exact And.intro
        (by
          rw [canonicalFingerprintRecognizedBlocksCNF_append]
          exact disjointSupport_append_right hleft.1
            (hcross b (List.Mem.head left)))
        (by
          apply ih hleft.2
          intro b' hb'
          exact hcross b' (List.Mem.tail b hb'))

/-- Disjointness can be restricted along a clause-list subset on the left. -/
theorem disjointSupport_of_clause_subset_left
    {m : Nat} {sub full target : CNFModel.CNF m}
    (hsubset : forall c : CNFModel.Clause m,
      List.Mem c sub -> List.Mem c full)
    (hdisjoint : ParityEncoded.DisjointSupport full target) :
    ParityEncoded.DisjointSupport sub target := by
  intro v hvSub hvTarget
  unfold ParityEncoded.cnfSupport at hvSub
  have hexists := List.mem_bind.1 hvSub
  cases hexists with
  | intro c hcAnd =>
      cases hcAnd with
      | intro hcSub hvClause =>
          have hvFull : List.Mem v (ParityEncoded.cnfSupport full) := by
            unfold ParityEncoded.cnfSupport
            exact List.mem_bind.2
              (Exists.intro c (And.intro (hsubset c hcSub) hvClause))
          exact hdisjoint v hvFull hvTarget

/-- A block's CNF is a clause-list subset of the CNF covered by its block list. -/
theorem blockCNF_subset_canonicalFingerprintRecognizedBlocksCNF
    {m : Nat}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hb : List.Mem b blocks) :
    forall c : CNFModel.Clause m,
      List.Mem c b.blockCNF ->
        List.Mem c (canonicalFingerprintRecognizedBlocksCNF blocks) := by
  intro c hc
  unfold canonicalFingerprintRecognizedBlocksCNF
  exact List.mem_bind.2 (Exists.intro b (And.intro hb hc))

/-- Covered-CNF disjointness implies every block is disjoint from the target CNF. -/
theorem canonicalBlocksDisjointFromCNF_of_disjointCovered
    {m : Nat}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {target : CNFModel.CNF m}
    (hdisjoint : ParityEncoded.DisjointSupport
      (canonicalFingerprintRecognizedBlocksCNF blocks) target) :
    CanonicalBlocksDisjointFromCNF blocks target := by
  intro b hb
  exact disjointSupport_of_clause_subset_left
    (blockCNF_subset_canonicalFingerprintRecognizedBlocksCNF hb)
    hdisjoint

/--
Append-disjointness composes from ordinary disjointness between the two covered
CNFs.
-/
theorem CanonicalBlocksAppendDisjoint.append_of_disjointCovered
    {m : Nat}
    {left right : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hleft : CanonicalBlocksAppendDisjoint left)
    (hright : CanonicalBlocksAppendDisjoint right)
    (hcovered : ParityEncoded.DisjointSupport
      (canonicalFingerprintRecognizedBlocksCNF left)
      (canonicalFingerprintRecognizedBlocksCNF right)) :
    CanonicalBlocksAppendDisjoint (left ++ right) := by
  exact CanonicalBlocksAppendDisjoint.append hleft hright
    (canonicalBlocksDisjointFromCNF_of_disjointCovered hcovered)

/-- Stronger per-block syntactic recognition signals for canonical blocks. -/
def CanonicalBlocksSyntacticSignals {m : Nat} :
    List (CanonicalFingerprintRecognizedParityBlock m) -> Prop
  | [] => True
  | b :: blocks =>
      parityBlockRecognitionSignal b.blockCNF b.spec = true /\
        CanonicalBlocksSyntacticSignals blocks

/-- Executable check that every canonical block can be upgraded syntactically. -/
def CanonicalBlocksToSyntacticOk {m : Nat} :
    List (CanonicalFingerprintRecognizedParityBlock m) -> Prop
  | [] => True
  | b :: blocks =>
      b.toSyntactic?.isSome = true /\
        CanonicalBlocksToSyntacticOk blocks

/-- A singleton canonical block list passes when its executable check succeeds. -/
theorem CanonicalBlocksToSyntacticOk.singleton
    {m : Nat}
    (b : CanonicalFingerprintRecognizedParityBlock m)
    (h : b.toSyntactic?.isSome = true) :
    CanonicalBlocksToSyntacticOk [b] := by
  exact And.intro h True.intro

/-- Successful `toSyntactic?` checks compose over appended block lists. -/
theorem CanonicalBlocksToSyntacticOk.append
    {m : Nat}
    {left right : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hleft : CanonicalBlocksToSyntacticOk left)
    (hright : CanonicalBlocksToSyntacticOk right) :
    CanonicalBlocksToSyntacticOk (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons _b _left ih =>
      exact And.intro hleft.1 (ih hleft.2)

/--
Finite key-disjoint generated families have recognized support groups whose
emitted canonical blocks all pass the executable syntactic upgrade.  This
strengthens `groupsRecognized_exists_of_generatedKeyDisjointFamily` with the
certificate needed by the recognizer-complete semantic bridges.
-/
theorem groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedKeyDisjointFamily m f s) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) blocks /\
        CanonicalBlocksToSyntacticOk blocks /\
        List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s := by
  induction hfamily with
  | empty =>
      exact Exists.intro [] (And.intro True.intro
        (And.intro True.intro (List.Perm.refl [])))
  | snoc _hprefix hkeyDisjoint hcnf hnormal ih =>
      rename_i fPrefix _sPrefix vars charge _c _tail
      rcases ih with ⟨prefixBlocks, hprefixRecognized,
        hprefixSyntactic, hprefixGF2⟩
      rcases
        inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
          hcnf hnormal with
        ⟨block, hinfer, hsyntactic, hcompact⟩
      have hgroupsRight :
          groupClausesByCanonicalSupport (clausesForVertex vars charge) =
            [(GroupFrame.canonicalSupportKeyForVars vars,
              clausesForVertex vars charge)] :=
        GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
          hcnf
      have hgroupsAppend :
          groupClausesByCanonicalSupport
              (fPrefix ++ clausesForVertex vars charge) =
            groupClausesByCanonicalSupport fPrefix ++
              [(GroupFrame.canonicalSupportKeyForVars vars,
                clausesForVertex vars charge)] := by
        have hframe :=
          GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
            fPrefix (clausesForVertex vars charge) hkeyDisjoint
        rw [hgroupsRight] at hframe
        exact hframe
      refine Exists.intro (prefixBlocks ++ [block]) ?_
      constructor
      · rw [hgroupsAppend]
        exact
          ExtractorCompleteness.GroupsRecognized.append
            hprefixRecognized (And.intro hinfer True.intro)
      constructor
      · exact
          CanonicalBlocksToSyntacticOk.append hprefixSyntactic
            (CanonicalBlocksToSyntacticOk.singleton block hsyntactic)
      · rw [canonicalFingerprintRecognizedBlocksGF2_append]
        simp [canonicalFingerprintRecognizedBlocksGF2, hcompact]
        exact hprefixGF2.append_right [parityClauseForVertex vars charge]

/--
Generated key-disjoint spec lists have recognized support groups, syntactic
upgrade certificates for all emitted blocks, and the expected folded GF(2)
output up to permutation.
-/
theorem groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport (generatedParitySpecsCNF specs))
        blocks /\
        CanonicalBlocksToSyntacticOk blocks /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 blocks)
          (generatedParitySpecsGF2 specs) :=
  groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointFamily
    (generatedKeyDisjointFamily_of_specList hspecs)

/--
Generated spec lists with fresh canonical support keys inherit the recognized
group and syntactic-upgrade certificate package.
-/
theorem groupsRecognizedWithSyntacticOk_exists_of_generatedCanonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport (generatedParitySpecsCNF specs))
        blocks /\
        CanonicalBlocksToSyntacticOk blocks /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 blocks)
          (generatedParitySpecsGF2 specs) :=
  groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointSpecList
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Successful `toSyntactic?` checks supply the syntactic-signal certificate needed
by the class bridge.
-/
theorem CanonicalBlocksSyntacticSignals.of_toSyntacticOk
    {m : Nat} {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (h : CanonicalBlocksToSyntacticOk blocks) :
    CanonicalBlocksSyntacticSignals blocks := by
  induction blocks with
  | nil => exact True.intro
  | cons b blocks ih =>
      change parityBlockRecognitionSignal b.blockCNF b.spec = true /\
        CanonicalBlocksSyntacticSignals blocks
      have hhead : b.toSyntactic?.isSome = true := h.1
      have htail : CanonicalBlocksToSyntacticOk blocks := h.2
      constructor
      case left =>
        unfold CanonicalFingerprintRecognizedParityBlock.toSyntactic? at hhead
        by_cases hsignal :
            parityBlockRecognitionSignal b.blockCNF b.spec = true
        case pos =>
          exact hsignal
        case neg =>
          simp [hsignal] at hhead
      case right =>
        exact ih htail

/--
Canonical block obtained from a generated parity spec.  This is the
specification-side fallback target: if a same-support component is later split
back into its generated parity specs, each spec already has a canonical
recognized block.
-/
def canonicalBlockFromGeneratedParitySpec {m : Nat}
    (spec : GeneratedParitySpec m) :
    CanonicalFingerprintRecognizedParityBlock m :=
  { blockCNF := generatedParitySpecCNF spec
    spec := { vars := spec.1, charge := spec.2 }
    fingerprintSignal :=
      canonicalParityBlockRecognitionSignal_clausesForVertex_self spec.1 spec.2 }

/-- Canonical fallback blocks obtained pointwise from generated parity specs. -/
def canonicalBlocksFromGeneratedParitySpecs {m : Nat}
    (specs : List (GeneratedParitySpec m)) :
    List (CanonicalFingerprintRecognizedParityBlock m) :=
  specs.map canonicalBlockFromGeneratedParitySpec

/--
Canonical fallback blocks remember the exact charge sequence from their
generated parity specs.  This is a block-level multiplicity invariant, before
the blocks are compacted to GF(2).
-/
theorem canonicalBlocksFromGeneratedParitySpecs_spec_charges_eq
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    ((canonicalBlocksFromGeneratedParitySpecs specs).map
        (fun b => b.spec.charge)) =
      specs.map (fun spec => spec.2) := by
  induction specs with
  | nil =>
      simp [canonicalBlocksFromGeneratedParitySpecs]
  | cons spec specs ih =>
      cases spec with
      | mk vars charge =>
          simp [canonicalBlocksFromGeneratedParitySpecs,
            canonicalBlockFromGeneratedParitySpec, ih]

/--
For generated same-support charges, canonical fallback blocks project back to
the exact input charge sequence.
-/
theorem canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_eq
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((canonicalBlocksFromGeneratedParitySpecs
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun b => b.spec.charge)) = charges := by
  rw [canonicalBlocksFromGeneratedParitySpecs_spec_charges_eq]
  simp [generatedParitySpecsForSupportCharges]

/-- Canonical fallback blocks preserve true-charge multiplicity. -/
theorem canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_true
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((canonicalBlocksFromGeneratedParitySpecs
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun b => b.spec.charge)).count true = charges.count true := by
  rw [canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_eq]

/-- Canonical fallback blocks preserve false-charge multiplicity. -/
theorem canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_false
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((canonicalBlocksFromGeneratedParitySpecs
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun b => b.spec.charge)).count false = charges.count false := by
  rw [canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_eq]

/--
The all-false clause fingerprint signal recovers the charge sequence from
generated same-support canonical fallback blocks.
-/
theorem canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_signals_eq
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((canonicalBlocksFromGeneratedParitySpecs
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun b =>
          (canonicalBlockFingerprint b.blockCNF).contains
            (canonicalClauseFingerprint
              (clauseForAssignment vars (List.replicate vars.length false))))) =
      charges := by
  induction charges with
  | nil =>
      simp [generatedParitySpecsForSupportCharges,
        canonicalBlocksFromGeneratedParitySpecs]
  | cons charge charges ih =>
      cases charge
      · change
          (canonicalBlockFingerprint (clausesForVertex vars false)).contains
              (canonicalClauseFingerprint
                (clauseForAssignment vars (List.replicate vars.length false))) ::
            ((canonicalBlocksFromGeneratedParitySpecs
              (generatedParitySpecsForSupportCharges vars charges)).map
                (fun b =>
                  (canonicalBlockFingerprint b.blockCNF).contains
                    (canonicalClauseFingerprint
                      (clauseForAssignment vars
                        (List.replicate vars.length false))))) =
            false :: charges
        rw [allFalseClauseFingerprint_signal_clausesForVertex_eq_charge, ih]
      · change
          (canonicalBlockFingerprint (clausesForVertex vars true)).contains
              (canonicalClauseFingerprint
                (clauseForAssignment vars (List.replicate vars.length false))) ::
            ((canonicalBlocksFromGeneratedParitySpecs
              (generatedParitySpecsForSupportCharges vars charges)).map
                (fun b =>
                  (canonicalBlockFingerprint b.blockCNF).contains
                    (canonicalClauseFingerprint
                      (clauseForAssignment vars
                        (List.replicate vars.length false))))) =
            true :: charges
        rw [allFalseClauseFingerprint_signal_clausesForVertex_eq_charge, ih]

/--
The all-false fingerprint signal counts true charges in generated same-support
canonical fallback blocks.
-/
theorem canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_count_true
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((canonicalBlocksFromGeneratedParitySpecs
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun b =>
          (canonicalBlockFingerprint b.blockCNF).contains
            (canonicalClauseFingerprint
              (clauseForAssignment vars (List.replicate vars.length false))))).count true =
      charges.count true := by
  rw [canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_signals_eq]

/--
The all-false fingerprint signal counts false charges in generated same-support
canonical fallback blocks.
-/
theorem canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_count_false
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((canonicalBlocksFromGeneratedParitySpecs
      (generatedParitySpecsForSupportCharges vars charges)).map
        (fun b =>
          (canonicalBlockFingerprint b.blockCNF).contains
            (canonicalClauseFingerprint
              (clauseForAssignment vars (List.replicate vars.length false))))).count false =
      charges.count false := by
  rw [canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_signals_eq]

/-- Fallback canonical blocks cover exactly the generated ordinary CNF fold. -/
theorem canonicalBlocksFromGeneratedParitySpecs_CNF_eq
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    canonicalFingerprintRecognizedBlocksCNF
      (canonicalBlocksFromGeneratedParitySpecs specs) =
      generatedParitySpecsCNF specs := by
  rw [generatedParitySpecsCNF_eq_bind]
  induction specs with
  | nil =>
      simp [canonicalBlocksFromGeneratedParitySpecs,
        canonicalFingerprintRecognizedBlocksCNF]
  | cons spec specs ih =>
      cases spec with
      | mk vars charge =>
          have htail :
              ((List.map canonicalBlockFromGeneratedParitySpec specs).bind
                fun b => b.blockCNF) = specs.bind generatedParitySpecCNF := by
            simpa [canonicalBlocksFromGeneratedParitySpecs,
              canonicalFingerprintRecognizedBlocksCNF] using ih
          simp [canonicalBlocksFromGeneratedParitySpecs,
            canonicalBlockFromGeneratedParitySpec,
            canonicalFingerprintRecognizedBlocksCNF,
            generatedParitySpecCNF, htail]

/-- Fallback canonical blocks compact exactly to the generated GF(2) fold. -/
theorem canonicalBlocksFromGeneratedParitySpecs_GF2_eq
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    canonicalFingerprintRecognizedBlocksGF2
      (canonicalBlocksFromGeneratedParitySpecs specs) =
      generatedParitySpecsGF2 specs := by
  rw [generatedParitySpecsGF2_eq_map]
  induction specs with
  | nil =>
      simp [canonicalBlocksFromGeneratedParitySpecs,
        canonicalFingerprintRecognizedBlocksGF2]
  | cons spec specs ih =>
      cases spec with
      | mk vars charge =>
          have htail := ih
          simp [canonicalBlocksFromGeneratedParitySpecs,
            canonicalFingerprintRecognizedBlocksGF2,
            CanonicalFingerprintRecognizedParityBlock.compactGF2,
            generatedParitySpecGF2] at htail
          simp [canonicalBlocksFromGeneratedParitySpecs,
            canonicalBlockFromGeneratedParitySpec,
            canonicalFingerprintRecognizedBlocksGF2,
            CanonicalFingerprintRecognizedParityBlock.compactGF2,
            generatedParitySpecGF2, htail]

/-- Each generated-spec fallback block passes the executable syntactic upgrade. -/
theorem canonicalBlockFromGeneratedParitySpec_toSyntacticOk
    {m : Nat} (spec : GeneratedParitySpec m) :
    (canonicalBlockFromGeneratedParitySpec spec).toSyntactic?.isSome = true := by
  cases spec with
  | mk vars charge =>
      exact
        canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal
          (canonicalBlockFromGeneratedParitySpec (vars, charge))
          (parityBlockRecognitionSignal_clausesForVertex_self vars charge)

/-- Generated-spec fallback block lists pass the executable syntactic upgrade. -/
theorem canonicalBlocksFromGeneratedParitySpecs_toSyntacticOk
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    CanonicalBlocksToSyntacticOk
      (canonicalBlocksFromGeneratedParitySpecs specs) := by
  induction specs with
  | nil =>
      simp [canonicalBlocksFromGeneratedParitySpecs, CanonicalBlocksToSyntacticOk]
  | cons spec specs ih =>
      change
        (canonicalBlockFromGeneratedParitySpec spec).toSyntactic?.isSome = true /\
          CanonicalBlocksToSyntacticOk
            (canonicalBlocksFromGeneratedParitySpecs specs)
      exact And.intro
        (canonicalBlockFromGeneratedParitySpec_toSyntacticOk spec) ih

/--
Specification target for the two-cycle same-support fallback: two generated
parity specs become two canonical recognized blocks, even though the current
support-key splitter merges their clauses into one unrecognized group.
-/
def twoCycleSameSupportFallbackBlocks :
    List (CanonicalFingerprintRecognizedParityBlock
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m) :=
  canonicalBlocksFromGeneratedParitySpecs
    (generatedParitySpecsForCycle 2 (by decide))

/-- The two-cycle same-support fallback has exactly two generated blocks. -/
theorem twoCycleSameSupportFallbackBlocks_length :
    twoCycleSameSupportFallbackBlocks.length = 2 := by
  decide

/-- The two-cycle same-support fallback blocks cover the direct two-cycle CNF. -/
theorem twoCycleSameSupportFallbackBlocks_CNF_eq :
    canonicalFingerprintRecognizedBlocksCNF twoCycleSameSupportFallbackBlocks =
      TseitinCycleCNFFormula 2 (by decide) := by
  unfold twoCycleSameSupportFallbackBlocks
  rw [canonicalBlocksFromGeneratedParitySpecs_CNF_eq]
  simpa [generatedParitySpecsForCycle, TseitinCycleCNFFormula] using
    (generatedParitySpecsCNF_fromEncoding
      (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)

/--
The two-cycle same-support fallback blocks compact to the direct two-equation
GF(2) target.
-/
theorem twoCycleSameSupportFallbackBlocks_GF2_eq :
    canonicalFingerprintRecognizedBlocksGF2 twoCycleSameSupportFallbackBlocks =
      TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge := by
  unfold twoCycleSameSupportFallbackBlocks
  rw [canonicalBlocksFromGeneratedParitySpecs_GF2_eq]
  simpa [generatedParitySpecsForCycle] using
    (generatedParitySpecsGF2_fromEncoding
      (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)

/-- The two-cycle same-support fallback blocks pass the syntactic upgrade. -/
theorem twoCycleSameSupportFallbackBlocks_toSyntacticOk :
    CanonicalBlocksToSyntacticOk twoCycleSameSupportFallbackBlocks := by
  unfold twoCycleSameSupportFallbackBlocks
  exact canonicalBlocksFromGeneratedParitySpecs_toSyntacticOk _

/--
Existence package for the two-cycle same-support fallback target.  The current
production splitter is certified not to find these blocks; this theorem states
the constructive target a same-support splitter should recover.
-/
theorem twoCycleSameSupportFallback_exists :
    exists blocks :
      List (CanonicalFingerprintRecognizedParityBlock
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived 2 (by decide))).m),
      blocks.length = 2 /\
      canonicalFingerprintRecognizedBlocksCNF blocks =
        TseitinCycleCNFFormula 2 (by decide) /\
      canonicalFingerprintRecognizedBlocksGF2 blocks =
        TseitinParityFormulaFromEncoding
          (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge /\
      CanonicalBlocksToSyntacticOk blocks := by
  refine ⟨twoCycleSameSupportFallbackBlocks, ?_⟩
  exact And.intro twoCycleSameSupportFallbackBlocks_length
    (And.intro twoCycleSameSupportFallbackBlocks_CNF_eq
      (And.intro twoCycleSameSupportFallbackBlocks_GF2_eq
        twoCycleSameSupportFallbackBlocks_toSyntacticOk))

/--
Specification-side fallback decomposition from generated parity specs.  This
uses the same residual-carrying structure as the production canonical splitter,
but its blocks are provided by the generated-spec specification rather than
found by an executable same-support recovery pass.
-/
def generatedParitySpecsFallbackDecomposition {m : Nat}
    (specs : List (GeneratedParitySpec m)) :
    CanonicalFingerprintGF2Decomposition m :=
  { blocks := canonicalBlocksFromGeneratedParitySpecs specs
    residualCNF := [] }

/-- Generated-spec fallback decompositions are residual-free. -/
theorem generatedParitySpecsFallbackDecomposition_hasEmptyResidual
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    (generatedParitySpecsFallbackDecomposition specs).hasEmptyResidual := by
  rfl

/-- The fallback decomposition core CNF is exactly the generated CNF fold. -/
theorem generatedParitySpecsFallbackDecomposition_coreCNF_eq
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    (generatedParitySpecsFallbackDecomposition specs).coreCNF =
      generatedParitySpecsCNF specs := by
  exact canonicalBlocksFromGeneratedParitySpecs_CNF_eq specs

/-- The fallback decomposition expanded CNF is exactly the generated CNF fold. -/
theorem generatedParitySpecsFallbackDecomposition_expandedCNF_eq
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    (generatedParitySpecsFallbackDecomposition specs).expandedCNF =
      generatedParitySpecsCNF specs := by
  simp [generatedParitySpecsFallbackDecomposition,
    CanonicalFingerprintGF2Decomposition.expandedCNF,
    CanonicalFingerprintGF2Decomposition.coreCNF,
    canonicalBlocksFromGeneratedParitySpecs_CNF_eq]

/-- The fallback decomposition compact GF(2) core is the generated GF(2) fold. -/
theorem generatedParitySpecsFallbackDecomposition_coreGF2_eq
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    (generatedParitySpecsFallbackDecomposition specs).coreGF2 =
      generatedParitySpecsGF2 specs := by
  exact canonicalBlocksFromGeneratedParitySpecs_GF2_eq specs

/--
For generated same-support charges, the fallback decomposition compact core
preserves the exact RHS charge list.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_eq
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).coreGF2.map
        (fun c => c.rhs)) = charges := by
  rw [generatedParitySpecsFallbackDecomposition_coreGF2_eq]
  exact generatedParitySpecsGF2_forSupportCharges_rhs_eq vars charges

/--
For generated same-support charges, the fallback decomposition compact core
preserves true-charge multiplicity.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_count_true
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).coreGF2.map
        (fun c => c.rhs)).count true = charges.count true := by
  rw [generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_eq]

/--
For generated same-support charges, the fallback decomposition compact core
preserves false-charge multiplicity.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_count_false
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).coreGF2.map
        (fun c => c.rhs)).count false = charges.count false := by
  rw [generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_eq]

/--
For generated same-support charges, the fallback decomposition block list
preserves the exact recognized-block charge sequence.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_eq
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).blocks.map
        (fun b => b.spec.charge)) = charges := by
  exact
    canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_eq
      vars charges

/--
For generated same-support charges, the fallback decomposition block list
preserves true-charge multiplicity.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_count_true
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).blocks.map
        (fun b => b.spec.charge)).count true = charges.count true := by
  rw [generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_eq]

/--
For generated same-support charges, the fallback decomposition block list
preserves false-charge multiplicity.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_count_false
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).blocks.map
        (fun b => b.spec.charge)).count false = charges.count false := by
  rw [generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_eq]

/--
For generated same-support charges, the fallback decomposition block
fingerprints expose the exact charge sequence through the all-false clause
fingerprint signal.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_signals_eq
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).blocks.map
        (fun b =>
          (canonicalBlockFingerprint b.blockCNF).contains
            (canonicalClauseFingerprint
              (clauseForAssignment vars (List.replicate vars.length false))))) =
      charges := by
  exact
    canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_signals_eq
      vars charges

/--
For generated same-support charges, the fallback decomposition all-false
fingerprint signal preserves true-charge multiplicity.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_count_true
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).blocks.map
        (fun b =>
          (canonicalBlockFingerprint b.blockCNF).contains
            (canonicalClauseFingerprint
              (clauseForAssignment vars (List.replicate vars.length false))))).count true =
      charges.count true := by
  rw [generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_signals_eq]

/--
For generated same-support charges, the fallback decomposition all-false
fingerprint signal preserves false-charge multiplicity.
-/
theorem generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_count_false
    {m : Nat} (vars : List (Fin m)) (charges : List Bool) :
    ((generatedParitySpecsFallbackDecomposition
      (generatedParitySpecsForSupportCharges vars charges)).blocks.map
        (fun b =>
          (canonicalBlockFingerprint b.blockCNF).contains
            (canonicalClauseFingerprint
              (clauseForAssignment vars (List.replicate vars.length false))))).count false =
      charges.count false := by
  rw [generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_signals_eq]

/-- The fallback decomposition blocks pass the executable syntactic upgrade. -/
theorem generatedParitySpecsFallbackDecomposition_toSyntacticOk
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    CanonicalBlocksToSyntacticOk
      (generatedParitySpecsFallbackDecomposition specs).blocks := by
  exact canonicalBlocksFromGeneratedParitySpecs_toSyntacticOk specs

/-- The fallback decomposition emits one compact equation per generated spec. -/
theorem generatedParitySpecsFallbackDecomposition_coreEquationCount
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    (generatedParitySpecsFallbackDecomposition specs).coreEquationCount =
      specs.length := by
  simp [generatedParitySpecsFallbackDecomposition,
    CanonicalFingerprintGF2Decomposition.coreEquationCount,
    canonicalBlocksFromGeneratedParitySpecs]

/-- The fallback decomposition has no residual ordinary clauses. -/
theorem generatedParitySpecsFallbackDecomposition_residualClauseCount
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    (generatedParitySpecsFallbackDecomposition specs).residualClauseCount = 0 := by
  rfl

/-- Expanded fallback clause count is inherited from the generated CNF fold. -/
theorem generatedParitySpecsFallbackDecomposition_expandedClauseCount
    {m : Nat} (specs : List (GeneratedParitySpec m)) :
    (generatedParitySpecsFallbackDecomposition specs).expandedCNF.length =
      (generatedParitySpecsCNF specs).length := by
  rw [generatedParitySpecsFallbackDecomposition_expandedCNF_eq]

/--
Decomposition-level target for the two-cycle same-support fallback.  This is
the residual-free shape a future executable splitter must recover for the
certified two-cycle failure case.
-/
def twoCycleSameSupportFallbackDecomposition :
    CanonicalFingerprintGF2Decomposition
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m :=
  generatedParitySpecsFallbackDecomposition
    (generatedParitySpecsForCycle 2 (by decide))

/-- The two-cycle same-support fallback decomposition is residual-free. -/
theorem twoCycleSameSupportFallbackDecomposition_hasEmptyResidual :
    twoCycleSameSupportFallbackDecomposition.hasEmptyResidual := by
  rfl

/-- The two-cycle same-support fallback decomposition covers the direct CNF. -/
theorem twoCycleSameSupportFallbackDecomposition_expandedCNF_eq :
    twoCycleSameSupportFallbackDecomposition.expandedCNF =
      TseitinCycleCNFFormula 2 (by decide) := by
  unfold twoCycleSameSupportFallbackDecomposition
  rw [generatedParitySpecsFallbackDecomposition_expandedCNF_eq]
  simpa [generatedParitySpecsForCycle, TseitinCycleCNFFormula] using
    (generatedParitySpecsCNF_fromEncoding
      (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)

/-- The two-cycle same-support fallback compacts to the direct GF(2) target. -/
theorem twoCycleSameSupportFallbackDecomposition_coreGF2_eq :
    twoCycleSameSupportFallbackDecomposition.coreGF2 =
      TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge := by
  unfold twoCycleSameSupportFallbackDecomposition
  rw [generatedParitySpecsFallbackDecomposition_coreGF2_eq]
  simpa [generatedParitySpecsForCycle] using
    (generatedParitySpecsGF2_fromEncoding
      (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)

/-- The two-cycle fallback decomposition blocks pass the syntactic upgrade. -/
theorem twoCycleSameSupportFallbackDecomposition_toSyntacticOk :
    CanonicalBlocksToSyntacticOk
      twoCycleSameSupportFallbackDecomposition.blocks := by
  unfold twoCycleSameSupportFallbackDecomposition
  exact generatedParitySpecsFallbackDecomposition_toSyntacticOk _

/-- The two-cycle fallback decomposition emits exactly two equations. -/
theorem twoCycleSameSupportFallbackDecomposition_coreEquationCount :
    twoCycleSameSupportFallbackDecomposition.coreEquationCount = 2 := by
  decide

/-- The two-cycle fallback decomposition has zero residual clauses. -/
theorem twoCycleSameSupportFallbackDecomposition_residualClauseCount :
    twoCycleSameSupportFallbackDecomposition.residualClauseCount = 0 := by
  rfl

/-- The two-cycle fallback decomposition covers sixteen expanded clauses. -/
theorem twoCycleSameSupportFallbackDecomposition_coreExpandedClauseCount :
    twoCycleSameSupportFallbackDecomposition.coreExpandedClauseCount = 16 := by
  decide

/-- The two-cycle fallback expanded CNF has sixteen clauses. -/
theorem twoCycleSameSupportFallbackDecomposition_expandedClauseCount :
    twoCycleSameSupportFallbackDecomposition.expandedCNF.length = 16 := by
  rw [twoCycleSameSupportFallbackDecomposition_expandedCNF_eq]
  decide

/--
Guided executable same-support recovery.  Given a merged CNF component and a
candidate generated-spec split, return the residual-free fallback
decomposition only when the generated ordinary CNF fold exactly covers the
component.
-/
def recoverSameSupportGeneratedParitySpecs? {m : Nat}
    (groupCNF : CNFModel.CNF m)
    (specs : List (GeneratedParitySpec m)) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  if generatedParitySpecsCNF specs = groupCNF then
    some (generatedParitySpecsFallbackDecomposition specs)
  else
    none

/-- Exact CNF coverage makes guided same-support recovery succeed. -/
theorem recoverSameSupportGeneratedParitySpecs_eq_some_of_cnf_eq
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    (h : generatedParitySpecsCNF specs = groupCNF) :
    recoverSameSupportGeneratedParitySpecs? groupCNF specs =
      some (generatedParitySpecsFallbackDecomposition specs) := by
  unfold recoverSameSupportGeneratedParitySpecs?
  simp [h]

/--
Soundness of guided same-support recovery: any returned decomposition covers
the input component, has empty residual, and compacts to the supplied
generated-spec GF(2) fold.
-/
theorem recoverSameSupportGeneratedParitySpecs_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGeneratedParitySpecs? groupCNF specs = some d) :
    d.expandedCNF = groupCNF /\ d.hasEmptyResidual /\
      d.coreGF2 = generatedParitySpecsGF2 specs := by
  unfold recoverSameSupportGeneratedParitySpecs? at hrec
  split at hrec
  next hcover =>
    cases hrec
    exact And.intro
      (Eq.trans
        (generatedParitySpecsFallbackDecomposition_expandedCNF_eq specs) hcover)
      (And.intro
        (generatedParitySpecsFallbackDecomposition_hasEmptyResidual specs)
        (generatedParitySpecsFallbackDecomposition_coreGF2_eq specs))
  next _hcover =>
    cases hrec

/--
Guided same-support recovery only returns generated-spec fallback blocks, and
those blocks pass the executable syntactic upgrade.
-/
theorem recoverSameSupportGeneratedParitySpecs_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGeneratedParitySpecs? groupCNF specs = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGeneratedParitySpecs? at hrec
  split at hrec
  next _hcover =>
    cases hrec
    exact generatedParitySpecsFallbackDecomposition_toSyntacticOk specs
  next _hcover =>
    cases hrec

/--
Permutation-insensitive guided same-support recovery.  This variant accepts a
generated-spec split when its expanded CNF covers the component up to clause
permutation.  It records the theorem-forming fix for the exact-list
order-sensitivity of `recoverSameSupportGeneratedParitySpecs?`.
-/
def recoverSameSupportGeneratedParitySpecsPerm? {m : Nat}
    (groupCNF : CNFModel.CNF m)
    (specs : List (GeneratedParitySpec m)) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  if _h : List.Perm (generatedParitySpecsCNF specs) groupCNF then
    some (generatedParitySpecsFallbackDecomposition specs)
  else
    none

/-- Permutation coverage makes guided same-support recovery succeed. -/
theorem recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    (h : List.Perm (generatedParitySpecsCNF specs) groupCNF) :
    recoverSameSupportGeneratedParitySpecsPerm? groupCNF specs =
      some (generatedParitySpecsFallbackDecomposition specs) := by
  unfold recoverSameSupportGeneratedParitySpecsPerm?
  simp [h]

/--
Soundness of permutation-insensitive guided same-support recovery: any returned
decomposition covers the input component up to clause permutation, has empty
residual, and compacts to the supplied generated-spec GF(2) fold.
-/
theorem recoverSameSupportGeneratedParitySpecsPerm_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGeneratedParitySpecsPerm? groupCNF specs = some d) :
    List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual /\
      d.coreGF2 = generatedParitySpecsGF2 specs := by
  unfold recoverSameSupportGeneratedParitySpecsPerm? at hrec
  split at hrec
  next hcover =>
    cases hrec
    exact And.intro
      (by
        rw [generatedParitySpecsFallbackDecomposition_expandedCNF_eq]
        exact hcover)
      (And.intro
        (generatedParitySpecsFallbackDecomposition_hasEmptyResidual specs)
        (generatedParitySpecsFallbackDecomposition_coreGF2_eq specs))
  next _hcover =>
    cases hrec

/--
Permutation-insensitive guided same-support recovery only returns generated-spec
fallback blocks, and those blocks pass the executable syntactic upgrade.
-/
theorem recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGeneratedParitySpecsPerm? groupCNF specs = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGeneratedParitySpecsPerm? at hrec
  split at hrec
  next _hcover =>
    cases hrec
    exact generatedParitySpecsFallbackDecomposition_toSyntacticOk specs
  next _hcover =>
    cases hrec

/--
Guided recovery for the current same-support boundary shape: one canonical
support group that may contain multiple parity blocks sharing the same support.
Other group shapes are rejected by this local recovery pass.
-/
def recoverSingleMergedSupportGroupFromGeneratedSpecs? {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m))
    (specs : List (GeneratedParitySpec m)) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match groups with
  | [g] => recoverSameSupportGeneratedParitySpecs? g.2 specs
  | _ => none

/-- Soundness for guided recovery from a single merged support group. -/
theorem recoverSingleMergedSupportGroupFromGeneratedSpecs_sound
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromGeneratedSpecs? groups specs = some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ d.expandedCNF = g.2 /\ d.hasEmptyResidual /\
        d.coreGF2 = generatedParitySpecsGF2 specs := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromGeneratedSpecs? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecs? at hrec
          exact Exists.intro g
            (And.intro rfl
              (recoverSameSupportGeneratedParitySpecs_sound hrec))
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecs? at hrec
          cases hrec

/-- Guided single-group recovery returns syntactically upgradable blocks. -/
theorem recoverSingleMergedSupportGroupFromGeneratedSpecs_toSyntacticOk
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromGeneratedSpecs? groups specs = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromGeneratedSpecs? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecs? at hrec
          exact recoverSameSupportGeneratedParitySpecs_toSyntacticOk hrec
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecs? at hrec
          cases hrec

/--
Permutation-insensitive guided recovery for one merged canonical support group.
The spec list is still caller supplied; this only removes clause-order
sensitivity from the guided single-group path.
-/
def recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m))
    (specs : List (GeneratedParitySpec m)) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match groups with
  | [g] => recoverSameSupportGeneratedParitySpecsPerm? g.2 specs
  | _ => none

/--
Soundness for permutation-insensitive guided recovery from one merged support
group.
-/
theorem recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_sound
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? groups specs = some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ List.Perm d.expandedCNF g.2 /\ d.hasEmptyResidual /\
        d.coreGF2 = generatedParitySpecsGF2 specs := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? at hrec
          exact Exists.intro g
            (And.intro rfl
              (recoverSameSupportGeneratedParitySpecsPerm_sound hrec))
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? at hrec
          cases hrec

/--
Permutation-insensitive guided single-group recovery returns syntactically
upgradable blocks.
-/
theorem recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_toSyntacticOk
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? groups specs = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? at hrec
          exact recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk hrec
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? at hrec
          cases hrec

/--
Charge-guided same-support recovery.  The support is inferred from the merged
component, while the caller supplies only the charge list.  This separates
support discovery from charge/multiplicity discovery.
-/
def recoverSameSupportGeneratedParityChargesPerm? {m : Nat}
    (groupCNF : CNFModel.CNF m)
    (charges : List Bool) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  let vars := parityCandidateCanonicalSupportFromBlock groupCNF
  recoverSameSupportGeneratedParitySpecsPerm?
    groupCNF (generatedParitySpecsForSupportCharges vars charges)

/--
Soundness for charge-guided same-support recovery: any returned decomposition
covers the input component up to clause permutation, has empty residual, and
compacts to the generated GF(2) fold for the inferred support and supplied
charges.
-/
theorem recoverSameSupportGeneratedParityChargesPerm_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {charges : List Bool}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGeneratedParityChargesPerm? groupCNF charges = some d) :
    List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual /\
      d.coreGF2 =
        generatedParitySpecsGF2
          (generatedParitySpecsForSupportCharges
            (parityCandidateCanonicalSupportFromBlock groupCNF) charges) := by
  unfold recoverSameSupportGeneratedParityChargesPerm? at hrec
  exact recoverSameSupportGeneratedParitySpecsPerm_sound hrec

/-- Charge-guided same-support recovery returns syntactically upgradable blocks. -/
theorem recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {charges : List Bool}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGeneratedParityChargesPerm? groupCNF charges = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGeneratedParityChargesPerm? at hrec
  exact recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk hrec

/--
Charge-guided recovery for one merged canonical support group.  Other group
shapes remain outside this local pass.
-/
def recoverSingleMergedSupportGroupFromChargesPerm? {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m))
    (charges : List Bool) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match groups with
  | [g] => recoverSameSupportGeneratedParityChargesPerm? g.2 charges
  | _ => none

/-- Soundness for charge-guided recovery from one merged support group. -/
theorem recoverSingleMergedSupportGroupFromChargesPerm_sound
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {charges : List Bool}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromChargesPerm? groups charges = some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ List.Perm d.expandedCNF g.2 /\ d.hasEmptyResidual /\
        d.coreGF2 =
          generatedParitySpecsGF2
            (generatedParitySpecsForSupportCharges
              (parityCandidateCanonicalSupportFromBlock g.2) charges) := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromChargesPerm? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromChargesPerm? at hrec
          exact Exists.intro g
            (And.intro rfl
              (recoverSameSupportGeneratedParityChargesPerm_sound hrec))
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromChargesPerm? at hrec
          cases hrec

/-- Charge-guided single-group recovery returns syntactically upgradable blocks. -/
theorem recoverSingleMergedSupportGroupFromChargesPerm_toSyntacticOk
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {charges : List Bool}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromChargesPerm? groups charges = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromChargesPerm? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromChargesPerm? at hrec
          exact recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk hrec
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromChargesPerm? at hrec
          cases hrec

/--
Bounded charge-search recovery for one same-support component.  The support is
inferred from the component and the charge list is searched up to `maxCharges`.
-/
def recoverSameSupportGeneratedParityChargeSearchPerm? {m : Nat}
    (groupCNF : CNFModel.CNF m)
    (maxCharges : Nat) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  firstSome? (chargeListsUpTo maxCharges)
    (fun charges => recoverSameSupportGeneratedParityChargesPerm? groupCNF charges)

/--
Soundness for bounded charge-search recovery: any returned decomposition came
from one of the searched charge lists and is sound for the input component.
-/
theorem recoverSameSupportGeneratedParityChargeSearchPerm_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {maxCharges : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGeneratedParityChargeSearchPerm? groupCNF maxCharges =
        some d) :
    exists charges : List Bool,
      List.Mem charges (chargeListsUpTo maxCharges) /\
        List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual /\
          d.coreGF2 =
            generatedParitySpecsGF2
              (generatedParitySpecsForSupportCharges
                (parityCandidateCanonicalSupportFromBlock groupCNF) charges) := by
  unfold recoverSameSupportGeneratedParityChargeSearchPerm? at hrec
  rcases firstSome?_eq_some_imp_exists_mem hrec with
    ⟨charges, hmem, hchargeRec⟩
  rcases recoverSameSupportGeneratedParityChargesPerm_sound hchargeRec with
    ⟨hcover, hresidual, hgf2⟩
  exact ⟨charges, hmem, hcover, hresidual, hgf2⟩

/-- Bounded charge-search recovery returns syntactically upgradable blocks. -/
theorem recoverSameSupportGeneratedParityChargeSearchPerm_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {maxCharges : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGeneratedParityChargeSearchPerm? groupCNF maxCharges =
        some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGeneratedParityChargeSearchPerm? at hrec
  rcases firstSome?_eq_some_imp_exists_mem hrec with
    ⟨charges, _hmem, hchargeRec⟩
  exact recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk hchargeRec

/--
Bounded charge-search recovery for one merged canonical support group.  Other
group shapes remain outside this local pass.
-/
def recoverSingleMergedSupportGroupFromChargeSearchPerm? {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m))
    (maxCharges : Nat) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match groups with
  | [g] => recoverSameSupportGeneratedParityChargeSearchPerm? g.2 maxCharges
  | _ => none

/-- Soundness for bounded charge-search recovery from one merged support group. -/
theorem recoverSingleMergedSupportGroupFromChargeSearchPerm_sound
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {maxCharges : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromChargeSearchPerm? groups maxCharges =
        some d) :
    exists g : CanonicalSupportClauseGroup m,
      exists charges : List Bool,
        groups = [g] /\ List.Mem charges (chargeListsUpTo maxCharges) /\
          List.Perm d.expandedCNF g.2 /\ d.hasEmptyResidual /\
            d.coreGF2 =
              generatedParitySpecsGF2
                (generatedParitySpecsForSupportCharges
                  (parityCandidateCanonicalSupportFromBlock g.2) charges) := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromChargeSearchPerm? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromChargeSearchPerm? at hrec
          rcases recoverSameSupportGeneratedParityChargeSearchPerm_sound hrec with
            ⟨charges, hmem, hcover, hresidual, hgf2⟩
          exact ⟨g, charges, rfl, hmem, hcover, hresidual, hgf2⟩
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromChargeSearchPerm? at hrec
          cases hrec

/-- Bounded single-group charge-search recovery returns syntactically upgradable blocks. -/
theorem recoverSingleMergedSupportGroupFromChargeSearchPerm_toSyntacticOk
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {maxCharges : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromChargeSearchPerm? groups maxCharges =
        some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupFromChargeSearchPerm? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupFromChargeSearchPerm? at hrec
          exact recoverSameSupportGeneratedParityChargeSearchPerm_toSyntacticOk hrec
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupFromChargeSearchPerm? at hrec
          cases hrec

/-- Direct-CNF guided recovery at the two-cycle same-support boundary. -/
def twoCycleSameSupportDirectRecovery? :
    Option (CanonicalFingerprintGF2Decomposition
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m) :=
  recoverSameSupportGeneratedParitySpecs?
    (TseitinCycleCNFFormula 2 (by decide))
    (generatedParitySpecsForCycle 2 (by decide))

/-- Direct-CNF guided recovery returns the certified two-cycle fallback. -/
theorem twoCycleSameSupportDirectRecovery_eq_some :
    twoCycleSameSupportDirectRecovery? =
      some twoCycleSameSupportFallbackDecomposition := by
  unfold twoCycleSameSupportDirectRecovery?
  unfold twoCycleSameSupportFallbackDecomposition
  apply recoverSameSupportGeneratedParitySpecs_eq_some_of_cnf_eq
  simpa [generatedParitySpecsForCycle, TseitinCycleCNFFormula] using
    (generatedParitySpecsCNF_fromEncoding
      (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)

/-- Canonical support grouping of the direct two-cycle CNF. -/
def twoCycleCanonicalSupportGroups :
    List (CanonicalSupportClauseGroup
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m) :=
  groupClausesByCanonicalSupport (TseitinCycleCNFFormula 2 (by decide))

/--
Guided same-support recovery applied to the actual canonical support grouping
of the direct two-cycle CNF.
-/
def twoCycleSameSupportMergedSupportRecovery? :
    Option (CanonicalFingerprintGF2Decomposition
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m) :=
  recoverSingleMergedSupportGroupFromGeneratedSpecs?
    twoCycleCanonicalSupportGroups
    (generatedParitySpecsForCycle 2 (by decide))

/-- The direct two-cycle CNF groups into one merged canonical support group. -/
theorem twoCycleCanonicalSupportGroups_length :
    twoCycleCanonicalSupportGroups.length = 1 := by
  decide

/--
The guided same-support recovery succeeds on the actual two-cycle merged
support group that the current unguided splitter residualizes.
-/
theorem twoCycleSameSupportMergedSupportRecovery_isSome :
    twoCycleSameSupportMergedSupportRecovery?.isSome = true := by
  decide

/--
Candidate two-charge split inferred from a merged same-support component.  This
is the first unguided splitter shape: recover the canonical support from the
component itself, then test both parity charges over that support.
-/
def sameSupportTwoChargeCandidateSpecs {m : Nat}
    (groupCNF : CNFModel.CNF m) : List (GeneratedParitySpec m) :=
  let vars := parityCandidateCanonicalSupportFromBlock groupCNF
  [(vars, true), (vars, false)]

/--
Flipped candidate order for the two-charge same-support split.  The exact CNF
coverage check is order-sensitive, so the executable probe tries both block
orders while keeping the semantic target explicit.
-/
def sameSupportTwoChargeCandidateSpecsFlipped {m : Nat}
    (groupCNF : CNFModel.CNF m) : List (GeneratedParitySpec m) :=
  let vars := parityCandidateCanonicalSupportFromBlock groupCNF
  [(vars, false), (vars, true)]

/--
Unguided two-charge same-support recovery.  The only inferred data is the
canonical support of the merged component; the function then accepts exactly
when one of the two charge orders expands back to the input component.
-/
def recoverTwoChargeSameSupportGroup? {m : Nat}
    (groupCNF : CNFModel.CNF m) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match recoverSameSupportGeneratedParitySpecs?
      groupCNF (sameSupportTwoChargeCandidateSpecs groupCNF) with
  | some d => some d
  | none =>
      recoverSameSupportGeneratedParitySpecs?
        groupCNF (sameSupportTwoChargeCandidateSpecsFlipped groupCNF)

/--
Permutation-insensitive unguided two-charge same-support recovery.  It keeps
the same inferred two-charge candidates as `recoverTwoChargeSameSupportGroup?`,
but accepts either candidate when its generated CNF covers the component up to
clause permutation.
-/
def recoverTwoChargeSameSupportGroupPerm? {m : Nat}
    (groupCNF : CNFModel.CNF m) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match recoverSameSupportGeneratedParitySpecsPerm?
      groupCNF (sameSupportTwoChargeCandidateSpecs groupCNF) with
  | some d => some d
  | none =>
      recoverSameSupportGeneratedParitySpecsPerm?
        groupCNF (sameSupportTwoChargeCandidateSpecsFlipped groupCNF)

/--
Soundness for unguided two-charge same-support recovery.  Any returned
decomposition exactly covers the input component and has no residual clauses.
-/
theorem recoverTwoChargeSameSupportGroup_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroup? groupCNF = some d) :
    d.expandedCNF = groupCNF /\ d.hasEmptyResidual := by
  unfold recoverTwoChargeSameSupportGroup? at hrec
  cases hfirst :
      recoverSameSupportGeneratedParitySpecs?
        groupCNF (sameSupportTwoChargeCandidateSpecs groupCNF) with
  | some dfirst =>
      simp [hfirst] at hrec
      cases hrec
      have hsound := recoverSameSupportGeneratedParitySpecs_sound hfirst
      exact And.intro hsound.1 hsound.2.1
  | none =>
      simp [hfirst] at hrec
      have hsound := recoverSameSupportGeneratedParitySpecs_sound hrec
      exact And.intro hsound.1 hsound.2.1

/--
The unguided two-charge same-support recovery emits only syntactically
upgradable generated-spec fallback blocks.
-/
theorem recoverTwoChargeSameSupportGroup_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroup? groupCNF = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverTwoChargeSameSupportGroup? at hrec
  cases hfirst :
      recoverSameSupportGeneratedParitySpecs?
        groupCNF (sameSupportTwoChargeCandidateSpecs groupCNF) with
  | some dfirst =>
      simp [hfirst] at hrec
      cases hrec
      exact recoverSameSupportGeneratedParitySpecs_toSyntacticOk hfirst
  | none =>
      simp [hfirst] at hrec
      exact recoverSameSupportGeneratedParitySpecs_toSyntacticOk hrec

/--
Soundness for permutation-insensitive unguided two-charge same-support
recovery.  Any returned decomposition covers the input component up to clause
permutation and has no residual clauses.
-/
theorem recoverTwoChargeSameSupportGroupPerm_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroupPerm? groupCNF = some d) :
    List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual := by
  unfold recoverTwoChargeSameSupportGroupPerm? at hrec
  cases hfirst :
      recoverSameSupportGeneratedParitySpecsPerm?
        groupCNF (sameSupportTwoChargeCandidateSpecs groupCNF) with
  | some dfirst =>
      simp [hfirst] at hrec
      cases hrec
      have hsound := recoverSameSupportGeneratedParitySpecsPerm_sound hfirst
      exact And.intro hsound.1 hsound.2.1
  | none =>
      simp [hfirst] at hrec
      have hsound := recoverSameSupportGeneratedParitySpecsPerm_sound hrec
      exact And.intro hsound.1 hsound.2.1

/--
The permutation-insensitive unguided two-charge same-support recovery emits
only syntactically upgradable generated-spec fallback blocks.
-/
theorem recoverTwoChargeSameSupportGroupPerm_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroupPerm? groupCNF = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverTwoChargeSameSupportGroupPerm? at hrec
  cases hfirst :
      recoverSameSupportGeneratedParitySpecsPerm?
        groupCNF (sameSupportTwoChargeCandidateSpecs groupCNF) with
  | some dfirst =>
      simp [hfirst] at hrec
      cases hrec
      exact recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk hfirst
  | none =>
      simp [hfirst] at hrec
      exact recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk hrec

/--
Direct same-support recovery branch for generated arity-three and arity-four
components.  The candidate support is inferred from the component; the charge
representative is derived from component length and the all-false fingerprint
count.  Other arities remain outside this direct branch.
-/
def recoverSameSupportGroupWithDirectChargeFallback? {m : Nat}
    (groupCNF : CNFModel.CNF m) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  let vars := parityCandidateCanonicalSupportFromBlock groupCNF
  if vars.length = 3 then
    recoverSameSupportGeneratedParityChargesPerm? groupCNF
      (directSameSupportChargesFromTargetWithBlockSize vars groupCNF 4)
  else if vars.length = 4 then
    recoverSameSupportGeneratedParityChargesPerm? groupCNF
      (directSameSupportChargesFromTargetWithBlockSize vars groupCNF 8)
  else none

/--
Soundness for the direct same-support recovery branch.  Any returned
decomposition covers the input component up to clause permutation and leaves no
residual clauses.
-/
theorem recoverSameSupportGroupWithDirectChargeFallback_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGroupWithDirectChargeFallback? groupCNF = some d) :
    List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual := by
  unfold recoverSameSupportGroupWithDirectChargeFallback? at hrec
  set vars := parityCandidateCanonicalSupportFromBlock groupCNF
  by_cases hthree : vars.length = 3
  · simp [hthree] at hrec
    rcases recoverSameSupportGeneratedParityChargesPerm_sound hrec with
      ⟨hcover, hresidual, _hgf2⟩
    exact ⟨hcover, hresidual⟩
  · by_cases hfour : vars.length = 4
    · simp [hthree, hfour] at hrec
      rcases recoverSameSupportGeneratedParityChargesPerm_sound hrec with
        ⟨hcover, hresidual, _hgf2⟩
      exact ⟨hcover, hresidual⟩
    · simp [hthree, hfour] at hrec

/--
The direct same-support recovery branch returns syntactically upgradable blocks
whenever it succeeds.
-/
theorem recoverSameSupportGroupWithDirectChargeFallback_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGroupWithDirectChargeFallback? groupCNF = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGroupWithDirectChargeFallback? at hrec
  set vars := parityCandidateCanonicalSupportFromBlock groupCNF
  by_cases hthree : vars.length = 3
  · simp [hthree] at hrec
    exact recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk hrec
  · by_cases hfour : vars.length = 4
    · simp [hthree, hfour] at hrec
      exact recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk hrec
    · simp [hthree, hfour] at hrec

/--
Block-size-parameterized direct same-support recovery branch.  The candidate
support is still inferred from the component, but the caller supplies the
single generated parity-block CNF size used for length quotienting.
-/
def recoverSameSupportGroupWithDirectBlockSizeFallback? {m : Nat}
    (groupCNF : CNFModel.CNF m) (blockSize : Nat) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  let vars := parityCandidateCanonicalSupportFromBlock groupCNF
  if blockSize = 0 then none
  else
    recoverSameSupportGeneratedParityChargesPerm? groupCNF
      (directSameSupportChargesFromTargetWithBlockSize vars groupCNF blockSize)

/--
Soundness for the block-size-parameterized direct branch.  Any returned
decomposition covers the input component up to clause permutation and leaves no
residual clauses.
-/
theorem recoverSameSupportGroupWithDirectBlockSizeFallback_sound
    {m : Nat} {groupCNF : CNFModel.CNF m} {blockSize : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGroupWithDirectBlockSizeFallback? groupCNF blockSize = some d) :
    List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual := by
  unfold recoverSameSupportGroupWithDirectBlockSizeFallback? at hrec
  set vars := parityCandidateCanonicalSupportFromBlock groupCNF
  by_cases hzero : blockSize = 0
  · simp [hzero] at hrec
  · simp [hzero] at hrec
    rcases recoverSameSupportGeneratedParityChargesPerm_sound hrec with
      ⟨hcover, hresidual, _hgf2⟩
    exact ⟨hcover, hresidual⟩

/--
The block-size-parameterized direct branch returns syntactically upgradable
blocks whenever it succeeds.
-/
theorem recoverSameSupportGroupWithDirectBlockSizeFallback_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m} {blockSize : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGroupWithDirectBlockSizeFallback? groupCNF blockSize = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGroupWithDirectBlockSizeFallback? at hrec
  set vars := parityCandidateCanonicalSupportFromBlock groupCNF
  by_cases hzero : blockSize = 0
  · simp [hzero] at hrec
  · simp [hzero] at hrec
    exact recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk hrec

/--
Direct same-support recovery branch whose block size is inferred from the
candidate support arity.  It is still guarded by the block-size fallback's
zero-size check, so empty inferred support is rejected before recovery.
-/
def recoverSameSupportGroupWithDirectInferredBlockSizeFallback? {m : Nat}
    (groupCNF : CNFModel.CNF m) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  let vars := parityCandidateCanonicalSupportFromBlock groupCNF
  recoverSameSupportGroupWithDirectBlockSizeFallback? groupCNF
    (generatedParitySupportBlockSize vars)

/-- Soundness for the inferred-block-size direct branch. -/
theorem recoverSameSupportGroupWithDirectInferredBlockSizeFallback_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGroupWithDirectInferredBlockSizeFallback? groupCNF = some d) :
    List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual := by
  unfold recoverSameSupportGroupWithDirectInferredBlockSizeFallback? at hrec
  exact recoverSameSupportGroupWithDirectBlockSizeFallback_sound hrec

/--
The inferred-block-size direct branch returns syntactically upgradable blocks
whenever it succeeds.
-/
theorem recoverSameSupportGroupWithDirectInferredBlockSizeFallback_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGroupWithDirectInferredBlockSizeFallback? groupCNF = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGroupWithDirectInferredBlockSizeFallback? at hrec
  exact recoverSameSupportGroupWithDirectBlockSizeFallback_toSyntacticOk hrec

/--
Production-shaped same-support recovery branch.  It preserves the existing
two-charge fast path, then tries direct arity-three/four count-derived
recovery, then the support-size-derived direct branch, and only then falls back
to exhaustive bounded charge search using the component length as the search
bound.
-/
def recoverSameSupportGroupWithChargeSearchFallback? {m : Nat}
    (groupCNF : CNFModel.CNF m) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match recoverTwoChargeSameSupportGroupPerm? groupCNF with
  | some d => some d
  | none =>
      match recoverSameSupportGroupWithDirectChargeFallback? groupCNF with
      | some d => some d
      | none =>
          match recoverSameSupportGroupWithDirectInferredBlockSizeFallback? groupCNF with
          | some d => some d
          | none =>
              if groupCNF = [] then none
              else recoverSameSupportGeneratedParityChargeSearchPerm? groupCNF groupCNF.length

/--
Soundness for the production-shaped same-support recovery branch.  A returned
decomposition covers the input component up to clause permutation and leaves no
residual clauses.
-/
theorem recoverSameSupportGroupWithChargeSearchFallback_sound
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGroupWithChargeSearchFallback? groupCNF = some d) :
    List.Perm d.expandedCNF groupCNF /\ d.hasEmptyResidual := by
  unfold recoverSameSupportGroupWithChargeSearchFallback? at hrec
  cases htwo : recoverTwoChargeSameSupportGroupPerm? groupCNF with
  | some dTwo =>
      simp [htwo] at hrec
      cases hrec
      exact recoverTwoChargeSameSupportGroupPerm_sound htwo
  | none =>
      cases hdirect : recoverSameSupportGroupWithDirectChargeFallback? groupCNF with
      | some dDirect =>
          simp [htwo, hdirect] at hrec
          cases hrec
          exact recoverSameSupportGroupWithDirectChargeFallback_sound hdirect
      | none =>
          cases hinferred :
              recoverSameSupportGroupWithDirectInferredBlockSizeFallback? groupCNF with
          | some dInferred =>
              simp [htwo, hdirect, hinferred] at hrec
              cases hrec
              exact
                recoverSameSupportGroupWithDirectInferredBlockSizeFallback_sound
                  hinferred
          | none =>
              by_cases hempty : groupCNF = []
              · subst groupCNF
                simp [htwo, hdirect, hinferred] at hrec
              · simp [htwo, hdirect, hinferred, hempty] at hrec
                rcases recoverSameSupportGeneratedParityChargeSearchPerm_sound hrec with
                  ⟨_charges, _hmem, hcover, hresidual, _hgf2⟩
                exact ⟨hcover, hresidual⟩

/--
The production-shaped same-support recovery branch returns syntactically
upgradable blocks whenever it succeeds.
-/
theorem recoverSameSupportGroupWithChargeSearchFallback_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGroupWithChargeSearchFallback? groupCNF = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  unfold recoverSameSupportGroupWithChargeSearchFallback? at hrec
  cases htwo : recoverTwoChargeSameSupportGroupPerm? groupCNF with
  | some dTwo =>
      simp [htwo] at hrec
      cases hrec
      exact recoverTwoChargeSameSupportGroupPerm_toSyntacticOk htwo
  | none =>
      cases hdirect : recoverSameSupportGroupWithDirectChargeFallback? groupCNF with
      | some dDirect =>
          simp [htwo, hdirect] at hrec
          cases hrec
          exact recoverSameSupportGroupWithDirectChargeFallback_toSyntacticOk hdirect
      | none =>
          cases hinferred :
              recoverSameSupportGroupWithDirectInferredBlockSizeFallback? groupCNF with
          | some dInferred =>
              simp [htwo, hdirect, hinferred] at hrec
              cases hrec
              exact
                recoverSameSupportGroupWithDirectInferredBlockSizeFallback_toSyntacticOk
                  hinferred
          | none =>
              by_cases hempty : groupCNF = []
              · subst groupCNF
                simp [htwo, hdirect, hinferred] at hrec
              · simp [htwo, hdirect, hinferred, hempty] at hrec
                exact recoverSameSupportGeneratedParityChargeSearchPerm_toSyntacticOk hrec

/--
For a nonempty clause permutation of two generated parity specs over the same
canonical support, the two-charge same-support candidate generator recovers the
original support and canonical charge order.
-/
theorem sameSupportTwoChargeCandidateSpecs_eq_of_perm_generatedParitySpecs_two_sameSupport
    {m : Nat} {vars : List (Fin m)} {target : CNFModel.CNF m}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF [(vars, true), (vars, false)]))
    (hnonempty : target ≠ []) :
    sameSupportTwoChargeCandidateSpecs target =
      [(vars, true), (vars, false)] := by
  cases htarget : target with
  | nil =>
      exact False.elim (hnonempty htarget)
  | cons c tail =>
      have hpermCons :
          List.Perm (c :: tail)
            (generatedParitySpecsCNF [(vars, true), (vars, false)]) := by
        simpa [htarget] using hperm
      have htargetVars :
          GroupFrame.CNFClausesHaveCanonicalSupportVars
            (c :: tail) vars := by
        exact
          GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm
            hpermCons
            (cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_two_sameSupport
              vars true false hnormal)
      have hcandidate :
          parityCandidateCanonicalSupportFromBlock (c :: tail) = vars :=
        GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons
          (f := c :: tail) (vars := vars) (c := c) (tail := tail)
          htargetVars rfl
      simp [sameSupportTwoChargeCandidateSpecs, hcandidate]

/--
Any nonempty clause permutation of two generated parity specs over the same
canonical support still forms one executable canonical support group.
-/
theorem groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_two_sameSupport
    {m : Nat} {vars : List (Fin m)} {target : CNFModel.CNF m}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF [(vars, true), (vars, false)]))
    (hnonempty : target ≠ []) :
    groupClausesByCanonicalSupport target =
      [(GroupFrame.canonicalSupportKeyForVars vars, target)] := by
  cases htarget : target with
  | nil =>
      exact False.elim (hnonempty htarget)
  | cons c tail =>
      have hpermCons :
          List.Perm (c :: tail)
            (generatedParitySpecsCNF [(vars, true), (vars, false)]) := by
        simpa [htarget] using hperm
      have htargetVars :
          GroupFrame.CNFClausesHaveCanonicalSupportVars
            (c :: tail) vars := by
        exact
          GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm
            hpermCons
            (cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_two_sameSupport
              vars true false hnormal)
      change
        groupClausesByCanonicalSupport (c :: tail) =
          [(GroupFrame.canonicalSupportKeyForVars vars, c :: tail)]
      apply GroupFrame.groupClausesByCanonicalSupport_cons_eq_single_of_same_key
      ·
        have hcvars :
            canonicalClauseSupportVars c = vars :=
          htargetVars c (List.Mem.head tail)
        rw [canonicalClauseSupportKey, GroupFrame.canonicalSupportKeyForVars,
          hcvars, hnormal]
      ·
        intro d hd
        have hdvars :
            canonicalClauseSupportVars d = vars :=
          htargetVars d (List.Mem.tail c hd)
        rw [canonicalClauseSupportKey, GroupFrame.canonicalSupportKeyForVars,
          hdvars, hnormal]

/--
The public permutation-insensitive two-charge fallback succeeds on every
nonempty clause permutation of two generated parity specs over the same
canonical support.
-/
theorem recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_generatedParitySpecs_two_sameSupport
    {m : Nat} {vars : List (Fin m)} {target : CNFModel.CNF m}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF [(vars, true), (vars, false)]))
    (hnonempty : target ≠ []) :
    recoverTwoChargeSameSupportGroupPerm? target =
      some (generatedParitySpecsFallbackDecomposition
        [(vars, true), (vars, false)]) := by
  unfold recoverTwoChargeSameSupportGroupPerm?
  have hcand :
      sameSupportTwoChargeCandidateSpecs target =
        [(vars, true), (vars, false)] :=
    sameSupportTwoChargeCandidateSpecs_eq_of_perm_generatedParitySpecs_two_sameSupport
      hnormal hperm hnonempty
  have hcover :
      List.Perm
        (generatedParitySpecsCNF
          (sameSupportTwoChargeCandidateSpecs target))
        target := by
    rw [hcand]
    exact hperm.symm
  rw [recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm hcover]
  simp [hcand]

/--
Any nonempty clause permutation of a generated parity-spec list whose specs
all use the same canonical support forms one executable canonical support
group.  This is the grouping half of arbitrary same-support guided recovery;
finding the spec list remains a separate recognizer problem.
-/
theorem groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport
    {m : Nat} {vars : List (Fin m)}
    {specs : List (GeneratedParitySpec m)}
    {target : CNFModel.CNF m}
    (hsame : GeneratedParitySpecsSameSupportVars specs vars)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm : List.Perm target (generatedParitySpecsCNF specs))
    (hnonempty : target ≠ []) :
    groupClausesByCanonicalSupport target =
      [(GroupFrame.canonicalSupportKeyForVars vars, target)] := by
  cases htarget : target with
  | nil =>
      exact False.elim (hnonempty htarget)
  | cons c tail =>
      have hpermCons :
          List.Perm (c :: tail) (generatedParitySpecsCNF specs) := by
        simpa [htarget] using hperm
      have htargetVars :
          GroupFrame.CNFClausesHaveCanonicalSupportVars
            (c :: tail) vars := by
        exact
          GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm
            hpermCons
            (cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_sameSupport
              hsame hnormal)
      change
        groupClausesByCanonicalSupport (c :: tail) =
          [(GroupFrame.canonicalSupportKeyForVars vars, c :: tail)]
      apply GroupFrame.groupClausesByCanonicalSupport_cons_eq_single_of_same_key
      ·
        have hcvars :
            canonicalClauseSupportVars c = vars :=
          htargetVars c (List.Mem.head tail)
        rw [canonicalClauseSupportKey, GroupFrame.canonicalSupportKeyForVars,
          hcvars, hnormal]
      ·
        intro d hd
        have hdvars :
            canonicalClauseSupportVars d = vars :=
          htargetVars d (List.Mem.tail c hd)
        rw [canonicalClauseSupportKey, GroupFrame.canonicalSupportKeyForVars,
          hdvars, hnormal]

/--
For any nonempty clause permutation of a generated parity-spec list whose
specs all use one canonical support, the executable support candidate recovers
that support.  Charge/multiplicity discovery remains separate.
-/
theorem parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport
    {m : Nat} {vars : List (Fin m)}
    {specs : List (GeneratedParitySpec m)}
    {target : CNFModel.CNF m}
    (hsame : GeneratedParitySpecsSameSupportVars specs vars)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm : List.Perm target (generatedParitySpecsCNF specs))
    (hnonempty : target ≠ []) :
    parityCandidateCanonicalSupportFromBlock target = vars := by
  cases htarget : target with
  | nil =>
      exact False.elim (hnonempty htarget)
  | cons c tail =>
      have hpermCons :
          List.Perm (c :: tail) (generatedParitySpecsCNF specs) := by
        simpa [htarget] using hperm
      have htargetVars :
          GroupFrame.CNFClausesHaveCanonicalSupportVars
            (c :: tail) vars := by
        exact
          GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm
            hpermCons
            (cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_sameSupport
              hsame hnormal)
      exact
        GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons
          (f := c :: tail) (vars := vars) (c := c) (tail := tail)
          htargetVars rfl

/--
Permutation-insensitive guided single-group recovery succeeds for any nonempty
clause permutation of a supplied generated parity-spec list whose specs all use
one canonical support.
-/
theorem recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_eq_some_of_perm_generatedParitySpecs_sameSupport
    {m : Nat} {vars : List (Fin m)}
    {specs : List (GeneratedParitySpec m)}
    {target : CNFModel.CNF m}
    (hsame : GeneratedParitySpecsSameSupportVars specs vars)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm : List.Perm target (generatedParitySpecsCNF specs))
    (hnonempty : target ≠ []) :
    recoverSingleMergedSupportGroupFromGeneratedSpecsPerm?
        (groupClausesByCanonicalSupport target) specs =
      some (generatedParitySpecsFallbackDecomposition specs) := by
  have hgroups :
      groupClausesByCanonicalSupport target =
        [(GroupFrame.canonicalSupportKeyForVars vars, target)] :=
    groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  rw [hgroups]
  unfold recoverSingleMergedSupportGroupFromGeneratedSpecsPerm?
  exact recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm hperm.symm

/--
Charge-guided same-support recovery succeeds whenever the supplied charge list
is correct: the support itself is inferred from the component.
-/
theorem recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    recoverSameSupportGeneratedParityChargesPerm? target charges =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars charges)) := by
  unfold recoverSameSupportGeneratedParityChargesPerm?
  have hsame :
      GeneratedParitySpecsSameSupportVars
        (generatedParitySpecsForSupportCharges vars charges) vars :=
    generatedParitySpecsForSupportCharges_sameSupport vars charges
  have hsupport :
      parityCandidateCanonicalSupportFromBlock target = vars :=
    parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  rw [hsupport]
  exact recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm hperm.symm

/--
The one-group charge-guided recovery succeeds on the canonical support grouping
whenever the supplied charge list is correct.  The support is inferred; only
the charge list remains guidance.
-/
theorem recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    recoverSingleMergedSupportGroupFromChargesPerm?
        (groupClausesByCanonicalSupport target) charges =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars charges)) := by
  have hsame :
      GeneratedParitySpecsSameSupportVars
        (generatedParitySpecsForSupportCharges vars charges) vars :=
    generatedParitySpecsForSupportCharges_sameSupport vars charges
  have hgroups :
      groupClausesByCanonicalSupport target =
        [(GroupFrame.canonicalSupportKeyForVars vars, target)] :=
    groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  rw [hgroups]
  unfold recoverSingleMergedSupportGroupFromChargesPerm?
  exact
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges
      hnormal hperm hnonempty

/--
Block-size-generic direct same-support recovery succeeds using the charge list
computed from target length and all-false fingerprint count, provided callers
certify that every generated block over the support has positive length `k`.
No bounded charge-list enumeration is used in this theorem.
-/
theorem recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_of_block_length
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    {k : Nat}
    (hk : 0 < k)
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGeneratedParityChargesPerm? target
        (directSameSupportChargesFromTargetWithBlockSize vars target k) =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target k))) := by
  have hdirectPerm :=
    directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_of_block_length
      (vars := vars) (charges := charges) (target := target) hk hlen hperm
  have hcnfDirectHidden :=
    generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm
      vars hdirectPerm
  have hpermDirect :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars
            (directSameSupportChargesFromTargetWithBlockSize vars target k))) :=
    hperm.trans hcnfDirectHidden.symm
  exact
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges
      hnormal hpermDirect hnonempty

/--
Block-size-generic direct one-group recovery succeeds using the charge list
computed from target length and all-false fingerprint count.
-/
theorem recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_of_block_length
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    {k : Nat}
    (hk : 0 < k)
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSingleMergedSupportGroupFromChargesPerm?
        (groupClausesByCanonicalSupport target)
        (directSameSupportChargesFromTargetWithBlockSize vars target k) =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target k))) := by
  have hdirectPerm :=
    directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_of_block_length
      (vars := vars) (charges := charges) (target := target) hk hlen hperm
  have hcnfDirectHidden :=
    generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm
      vars hdirectPerm
  have hpermDirect :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars
            (directSameSupportChargesFromTargetWithBlockSize vars target k))) :=
    hperm.trans hcnfDirectHidden.symm
  exact
    recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges
      hnormal hpermDirect hnonempty

/--
The block-size-parameterized production-shaped direct branch succeeds on a
generated same-support component whenever callers certify the positive
generated block size `k`.
-/
theorem recoverSameSupportGroupWithDirectBlockSizeFallback_eq_some_of_directTargetCharges_of_block_length
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    {k : Nat}
    (hk : 0 < k)
    (hlen :
      forall charge : Bool, List.Mem charge charges ->
        (clausesForVertex vars charge).length = k)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGroupWithDirectBlockSizeFallback? target k =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target k))) := by
  unfold recoverSameSupportGroupWithDirectBlockSizeFallback?
  have hsame :
      GeneratedParitySpecsSameSupportVars
        (generatedParitySpecsForSupportCharges vars charges) vars :=
    generatedParitySpecsForSupportCharges_sameSupport vars charges
  have hsupport :
      parityCandidateCanonicalSupportFromBlock target = vars :=
    parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  have hzero : Not (k = 0) := Nat.ne_of_gt hk
  simp [hsupport, hzero]
  exact
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_of_block_length
      hk hlen hnormal hperm hnonempty

/--
The inferred-block-size direct branch succeeds on any nonempty generated
same-support component. The generated one-block CNF size is derived from the
support arity, so no arity-three/four specialization or bounded charge-list
enumeration is used in this theorem.
-/
theorem recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_of_directTargetCharges_supportSize
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : Not (vars = []))
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGroupWithDirectInferredBlockSizeFallback? target =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target
            (generatedParitySupportBlockSize vars)))) := by
  unfold recoverSameSupportGroupWithDirectInferredBlockSizeFallback?
  have hsame :
      GeneratedParitySpecsSameSupportVars
        (generatedParitySpecsForSupportCharges vars charges) vars :=
    generatedParitySpecsForSupportCharges_sameSupport vars charges
  have hsupport :
      parityCandidateCanonicalSupportFromBlock target = vars :=
    parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  rw [hsupport]
  exact
    recoverSameSupportGroupWithDirectBlockSizeFallback_eq_some_of_directTargetCharges_of_block_length
      (generatedParitySupportBlockSize_pos_of_vars_ne_empty hvars)
      (by
        intro charge _hmem
        exact clausesForVertex_length_eq_generatedParitySupportBlockSize
          (vars := vars) (charge := charge) hvars)
      hnormal hperm hnonempty

/--
Arity-three direct same-support recovery succeeds using the charge list computed
from target length and all-false fingerprint count.  No bounded charge-list
enumeration is used in this theorem.
-/
theorem recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityThree
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGeneratedParityChargesPerm? target
        (directSameSupportChargesFromTargetWithBlockSize vars target 4) =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 4))) := by
  have hdirectPerm :=
    directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityThree
      (vars := vars) (charges := charges) (target := target) hlen hperm
  have hcnfDirectHidden :=
    generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm
      vars hdirectPerm
  have hpermDirect :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars
            (directSameSupportChargesFromTargetWithBlockSize vars target 4))) :=
    hperm.trans hcnfDirectHidden.symm
  exact
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges
      hnormal hpermDirect hnonempty

/--
Arity-four direct same-support recovery succeeds using the charge list computed
from target length and all-false fingerprint count.  No bounded charge-list
enumeration is used in this theorem.
-/
theorem recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityFour
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGeneratedParityChargesPerm? target
        (directSameSupportChargesFromTargetWithBlockSize vars target 8) =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 8))) := by
  have hdirectPerm :=
    directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityFour
      (vars := vars) (charges := charges) (target := target) hlen hperm
  have hcnfDirectHidden :=
    generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm
      vars hdirectPerm
  have hpermDirect :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars
            (directSameSupportChargesFromTargetWithBlockSize vars target 8))) :=
    hperm.trans hcnfDirectHidden.symm
  exact
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges
      hnormal hpermDirect hnonempty

/--
Arity-three direct one-group recovery succeeds using the charge list computed
from target length and all-false fingerprint count.
-/
theorem recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityThree
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSingleMergedSupportGroupFromChargesPerm?
        (groupClausesByCanonicalSupport target)
        (directSameSupportChargesFromTargetWithBlockSize vars target 4) =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 4))) := by
  have hdirectPerm :=
    directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityThree
      (vars := vars) (charges := charges) (target := target) hlen hperm
  have hcnfDirectHidden :=
    generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm
      vars hdirectPerm
  have hpermDirect :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars
            (directSameSupportChargesFromTargetWithBlockSize vars target 4))) :=
    hperm.trans hcnfDirectHidden.symm
  exact
    recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges
      hnormal hpermDirect hnonempty

/--
Arity-four direct one-group recovery succeeds using the charge list computed
from target length and all-false fingerprint count.
-/
theorem recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityFour
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSingleMergedSupportGroupFromChargesPerm?
        (groupClausesByCanonicalSupport target)
        (directSameSupportChargesFromTargetWithBlockSize vars target 8) =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 8))) := by
  have hdirectPerm :=
    directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityFour
      (vars := vars) (charges := charges) (target := target) hlen hperm
  have hcnfDirectHidden :=
    generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm
      vars hdirectPerm
  have hpermDirect :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars
            (directSameSupportChargesFromTargetWithBlockSize vars target 8))) :=
    hperm.trans hcnfDirectHidden.symm
  exact
    recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges
      hnormal hpermDirect hnonempty

/--
The production direct same-support branch succeeds on generated arity-three
components using the count-derived charge representative.
-/
theorem recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityThree
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGroupWithDirectChargeFallback? target =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 4))) := by
  unfold recoverSameSupportGroupWithDirectChargeFallback?
  have hsame :
      GeneratedParitySpecsSameSupportVars
        (generatedParitySpecsForSupportCharges vars charges) vars :=
    generatedParitySpecsForSupportCharges_sameSupport vars charges
  have hsupport :
      parityCandidateCanonicalSupportFromBlock target = vars :=
    parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  rw [hsupport]
  simp [hlen,
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityThree
      hlen hnormal hperm hnonempty]

/--
The production direct same-support branch succeeds on generated arity-four
components using the count-derived charge representative.
-/
theorem recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityFour
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGroupWithDirectChargeFallback? target =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 8))) := by
  unfold recoverSameSupportGroupWithDirectChargeFallback?
  have hsame :
      GeneratedParitySpecsSameSupportVars
        (generatedParitySpecsForSupportCharges vars charges) vars :=
    generatedParitySpecsForSupportCharges_sameSupport vars charges
  have hsupport :
      parityCandidateCanonicalSupportFromBlock target = vars :=
    parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  rw [hsupport]
  simp [hlen,
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityFour
      hlen hnormal hperm hnonempty]

/--
If the legacy two-charge fast path misses, the production same-support branch
uses the direct count-derived arity-three branch before exhaustive search.
-/
theorem recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_arityThree_of_twoCharge_none
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = []))
    (htwo : recoverTwoChargeSameSupportGroupPerm? target = none) :
    recoverSameSupportGroupWithChargeSearchFallback? target =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 4))) := by
  unfold recoverSameSupportGroupWithChargeSearchFallback?
  have hdirect :=
    recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityThree
      hlen hnormal hperm hnonempty
  simp [htwo, hdirect]

/--
If the legacy two-charge fast path misses, the production same-support branch
uses the direct count-derived arity-four branch before exhaustive search.
-/
theorem recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_arityFour_of_twoCharge_none
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = []))
    (htwo : recoverTwoChargeSameSupportGroupPerm? target = none) :
    recoverSameSupportGroupWithChargeSearchFallback? target =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target 8))) := by
  unfold recoverSameSupportGroupWithChargeSearchFallback?
  have hdirect :=
    recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityFour
      hlen hnormal hperm hnonempty
  simp [htwo, hdirect]

/--
The production-shaped same-support fallback uses the inferred support-size
direct branch before exhaustive charge-list enumeration. This theorem records
the generic nonempty generated-support path when the two-charge fast path and
the older arity-three/four direct branch both miss.
-/
theorem recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_supportSize_of_twoCharge_none_of_directCharge_none
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : Not (vars = []))
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = []))
    (htwo : recoverTwoChargeSameSupportGroupPerm? target = none)
    (hdirect : recoverSameSupportGroupWithDirectChargeFallback? target = none) :
    recoverSameSupportGroupWithChargeSearchFallback? target =
      some (generatedParitySpecsFallbackDecomposition
        (generatedParitySpecsForSupportCharges vars
          (directSameSupportChargesFromTargetWithBlockSize vars target
            (generatedParitySupportBlockSize vars)))) := by
  unfold recoverSameSupportGroupWithChargeSearchFallback?
  have hinferred :=
    recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_of_directTargetCharges_supportSize
      hvars hnormal hperm hnonempty
  simp [htwo, hdirect, hinferred]

/--
For any nonempty generated same-support component, the production-shaped
same-support fallback is exhausted by its non-enumerative branches.  If the
two-charge fast path accepts, that result is returned; otherwise, if the older
arity-three/four direct branch accepts, that result is returned; otherwise the
inferred support-size direct branch returns the generated direct decomposition.
The exhaustive `chargeListsUpTo` branch is unreachable under these hypotheses.
-/
theorem recoverSameSupportGroupWithChargeSearchFallback_eq_nonexhaustive_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)} {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : Not (vars = []))
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : Not (target = [])) :
    recoverSameSupportGroupWithChargeSearchFallback? target =
      match recoverTwoChargeSameSupportGroupPerm? target with
      | some d => some d
      | none =>
          match recoverSameSupportGroupWithDirectChargeFallback? target with
          | some d => some d
          | none =>
              some (generatedParitySpecsFallbackDecomposition
                (generatedParitySpecsForSupportCharges vars
                  (directSameSupportChargesFromTargetWithBlockSize vars target
                    (generatedParitySupportBlockSize vars)))) := by
  unfold recoverSameSupportGroupWithChargeSearchFallback?
  cases htwo : recoverTwoChargeSameSupportGroupPerm? target with
  | some d =>
      simp [htwo]
  | none =>
      cases hdirect : recoverSameSupportGroupWithDirectChargeFallback? target with
      | some d =>
          simp [htwo, hdirect]
      | none =>
          have hinferred :=
            recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_of_directTargetCharges_supportSize
              hvars hnormal hperm hnonempty
          simp [htwo, hdirect, hinferred]

/--
Bounded charge-search recovery succeeds whenever the component is a
same-support generated parity expansion whose true charge list is within the
search bound.
-/
theorem recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    {maxCharges : Nat}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ [])
    (hle : charges.length <= maxCharges) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSameSupportGeneratedParityChargeSearchPerm? target maxCharges =
        some d := by
  unfold recoverSameSupportGeneratedParityChargeSearchPerm?
  have hmem : List.Mem charges (chargeListsUpTo maxCharges) :=
    mem_chargeListsUpTo_of_length_le hle
  have hchargeRec :
      recoverSameSupportGeneratedParityChargesPerm? target charges =
        some (generatedParitySpecsFallbackDecomposition
          (generatedParitySpecsForSupportCharges vars charges)) :=
    recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges
      hnormal hperm hnonempty
  exact firstSome?_exists_some_of_mem_eq_some hmem hchargeRec

/--
Bounded charge-search recovery succeeds on the canonical support grouping
whenever the correct charge list is within the search bound.
-/
theorem recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    {maxCharges : Nat}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ [])
    (hle : charges.length <= maxCharges) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSingleMergedSupportGroupFromChargeSearchPerm?
          (groupClausesByCanonicalSupport target) maxCharges =
        some d := by
  have hsame :
      GeneratedParitySpecsSameSupportVars
        (generatedParitySpecsForSupportCharges vars charges) vars :=
    generatedParitySpecsForSupportCharges_sameSupport vars charges
  have hgroups :
      groupClausesByCanonicalSupport target =
        [(GroupFrame.canonicalSupportKeyForVars vars, target)] :=
    groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport
      hsame hnormal hperm hnonempty
  rw [hgroups]
  unfold recoverSingleMergedSupportGroupFromChargeSearchPerm?
  exact
    recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges
      hnormal hperm hnonempty hle

/--
For nonempty-support generated same-support components, the component's own
clause count is a certified safe bound for bounded charge-search recovery.
-/
theorem recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_componentBound
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : vars ≠ [])
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSameSupportGeneratedParityChargeSearchPerm? target target.length =
        some d := by
  exact
    recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges
      hnormal hperm hnonempty
      (charges_length_le_of_perm_generatedParitySpecsForSupportCharges
        hvars hperm)

/--
For nonempty generated same-support components, the production-shaped
same-support branch succeeds: either the legacy two-charge fast path accepts,
the direct arity-three/four branch accepts, the inferred block-size branch
accepts, or the inferred support-size branch accepts.  Under these generated
component hypotheses, the exhaustive charge-search fallback is not needed.
-/
theorem recoverSameSupportGroupWithChargeSearchFallback_exists_of_perm_supportCharges_componentBound
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : vars ≠ [])
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSameSupportGroupWithChargeSearchFallback? target = some d := by
  have hprod :=
    recoverSameSupportGroupWithChargeSearchFallback_eq_nonexhaustive_of_perm_supportCharges
      hvars hnormal hperm hnonempty
  cases htwo : recoverTwoChargeSameSupportGroupPerm? target with
  | some d =>
      exact ⟨d, by simpa [htwo] using hprod⟩
  | none =>
      cases hdirect : recoverSameSupportGroupWithDirectChargeFallback? target with
      | some d =>
          exact ⟨d, by simpa [htwo, hdirect] using hprod⟩
      | none =>
          exact
            ⟨generatedParitySpecsFallbackDecomposition
              (generatedParitySpecsForSupportCharges vars
                (directSameSupportChargesFromTargetWithBlockSize vars target
                  (generatedParitySupportBlockSize vars))),
              by
                simpa [htwo, hdirect] using hprod⟩

/--
The same component-derived bound lifts through the canonical support grouping
wrapper for a single merged same-support component.
-/
theorem recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_componentBound
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hvars : vars ≠ [])
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSingleMergedSupportGroupFromChargeSearchPerm?
          (groupClausesByCanonicalSupport target) target.length =
        some d := by
  exact
    recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges
      hnormal hperm hnonempty
      (charges_length_le_of_perm_generatedParitySpecsForSupportCharges
        hvars hperm)

/--
For arity-three same-support generated components, the exact component quotient
`target.length / 4` is a certified charge-search bound.
-/
theorem recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSameSupportGeneratedParityChargeSearchPerm?
          target (target.length / 4) =
        some d := by
  exact
    recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges
      hnormal hperm hnonempty
      (Nat.le_of_eq
        (charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges
          (vars := vars) (charges := charges) (target := target) hlen hperm))

/--
The same arity-three quotient bound lifts through the canonical support grouping
wrapper for a single merged same-support component.
-/
theorem recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 3)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSingleMergedSupportGroupFromChargeSearchPerm?
          (groupClausesByCanonicalSupport target) (target.length / 4) =
        some d := by
  exact
    recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges
      hnormal hperm hnonempty
      (Nat.le_of_eq
        (charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges
          (vars := vars) (charges := charges) (target := target) hlen hperm))

/--
For arity-four same-support generated components, the exact component quotient
`target.length / 8` is a certified charge-search bound.
-/
theorem recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSameSupportGeneratedParityChargeSearchPerm?
          target (target.length / 8) =
        some d := by
  exact
    recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges
      hnormal hperm hnonempty
      (Nat.le_of_eq
        (charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges
          (vars := vars) (charges := charges) (target := target) hlen hperm))

/--
The same arity-four quotient bound lifts through the canonical support grouping
wrapper for a single merged same-support component.
-/
theorem recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound
    {m : Nat} {vars : List (Fin m)}
    {charges : List Bool}
    {target : CNFModel.CNF m}
    (hlen : vars.length = 4)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF
          (generatedParitySpecsForSupportCharges vars charges)))
    (hnonempty : target ≠ []) :
    exists d : CanonicalFingerprintGF2Decomposition m,
      recoverSingleMergedSupportGroupFromChargeSearchPerm?
          (groupClausesByCanonicalSupport target) (target.length / 8) =
        some d := by
  exact
    recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges
      hnormal hperm hnonempty
      (Nat.le_of_eq
        (charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges
          (vars := vars) (charges := charges) (target := target) hlen hperm))

/--
Unguided recovery for the one-merged-support-group boundary shape.  Other group
shapes remain outside this narrow local recovery pass.
-/
def recoverSingleMergedSupportGroupTwoCharge? {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) :
    Option (CanonicalFingerprintGF2Decomposition m) :=
  match groups with
  | [g] => recoverTwoChargeSameSupportGroup? g.2
  | _ => none

/-- Soundness for unguided recovery from a single merged support group. -/
theorem recoverSingleMergedSupportGroupTwoCharge_sound
    {m : Nat} {groups : List (CanonicalSupportClauseGroup m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSingleMergedSupportGroupTwoCharge? groups = some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ d.expandedCNF = g.2 /\ d.hasEmptyResidual := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupTwoCharge? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupTwoCharge? at hrec
          exact Exists.intro g
            (And.intro rfl (recoverTwoChargeSameSupportGroup_sound hrec))
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupTwoCharge? at hrec
          cases hrec

/-- Unguided single merged-group recovery returns syntactically upgradable blocks. -/
theorem recoverSingleMergedSupportGroupTwoCharge_toSyntacticOk
    {m : Nat} {groups : List (CanonicalSupportClauseGroup m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSingleMergedSupportGroupTwoCharge? groups = some d) :
    CanonicalBlocksToSyntacticOk d.blocks := by
  cases groups with
  | nil =>
      unfold recoverSingleMergedSupportGroupTwoCharge? at hrec
      cases hrec
  | cons g groups =>
      cases groups with
      | nil =>
          unfold recoverSingleMergedSupportGroupTwoCharge? at hrec
          exact recoverTwoChargeSameSupportGroup_toSyntacticOk hrec
      | cons _g2 _groups =>
          unfold recoverSingleMergedSupportGroupTwoCharge? at hrec
          cases hrec

/-- Direct-CNF unguided recovery at the two-cycle same-support boundary. -/
def twoCycleSameSupportUnguidedDirectRecovery? :
    Option (CanonicalFingerprintGF2Decomposition
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m) :=
  recoverTwoChargeSameSupportGroup? (TseitinCycleCNFFormula 2 (by decide))

/--
The two-charge candidate inferred from the direct two-cycle CNF is exactly the
generated two-spec target.
-/
theorem sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated :
    sameSupportTwoChargeCandidateSpecs (TseitinCycleCNFFormula 2 (by decide)) =
      generatedParitySpecsForCycle 2 (by decide) := by
  decide

/--
All direct two-cycle clauses share the support inferred from the first clause.
This is the support-stability fact needed to transport the two-charge fallback
candidate generator across arbitrary permutations of the merged component.
-/
theorem twoCycleCNF_clausesHaveCandidateSupportVars :
    GroupFrame.CNFClausesHaveCanonicalSupportVars
      (TseitinCycleCNFFormula 2 (by decide))
      (parityCandidateCanonicalSupportFromBlock
        (TseitinCycleCNFFormula 2 (by decide))) := by
  let vars :=
    parityCandidateCanonicalSupportFromBlock
      (TseitinCycleCNFFormula 2 (by decide))
  have hspecs :
      generatedParitySpecsForCycle 2 (by decide) =
        [(vars, true), (vars, false)] := by
    have h := sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated
    simpa [sameSupportTwoChargeCandidateSpecs, vars] using h.symm
  have hcnf :
      generatedParitySpecsCNF (generatedParitySpecsForCycle 2 (by decide)) =
        TseitinCycleCNFFormula 2 (by decide) := by
    simpa [generatedParitySpecsForCycle, TseitinCycleCNFFormula] using
      (generatedParitySpecsCNF_fromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)
  have hnormal : GroupFrame.VarsInCanonicalSupportOrder vars := by
    dsimp [vars]
    unfold GroupFrame.VarsInCanonicalSupportOrder
    decide
  change
    GroupFrame.CNFClausesHaveCanonicalSupportVars
      (TseitinCycleCNFFormula 2 (by decide)) vars
  rw [← hcnf, hspecs]
  exact
    cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_two_sameSupport
      vars true false hnormal

/--
Any nonempty clause permutation of the direct two-cycle CNF infers the same
two-charge generated-spec target as the direct component.
-/
theorem sameSupportTwoChargeCandidateSpecs_eq_generated_of_perm_twoCycle
    {target : CNFModel.CNF
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m}
    (hperm : List.Perm target (TseitinCycleCNFFormula 2 (by decide)))
    (hnonempty : target ≠ []) :
    sameSupportTwoChargeCandidateSpecs target =
      generatedParitySpecsForCycle 2 (by decide) := by
  let vars :=
    parityCandidateCanonicalSupportFromBlock
      (TseitinCycleCNFFormula 2 (by decide))
  have hspecs :
      generatedParitySpecsForCycle 2 (by decide) =
        [(vars, true), (vars, false)] := by
    have h := sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated
    simpa [sameSupportTwoChargeCandidateSpecs, vars] using h.symm
  cases htarget : target with
  | nil =>
      exact False.elim (hnonempty htarget)
  | cons c tail =>
      have hpermCons :
          List.Perm (c :: tail)
            (TseitinCycleCNFFormula 2 (by decide)) := by
        simpa [htarget] using hperm
      have htargetVars :
          GroupFrame.CNFClausesHaveCanonicalSupportVars
            (c :: tail) vars := by
        simpa [vars] using
          (GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm
            (f := c :: tail)
            (g := TseitinCycleCNFFormula 2 (by decide))
            hpermCons
            twoCycleCNF_clausesHaveCandidateSupportVars)
      have hcandidate :
          parityCandidateCanonicalSupportFromBlock (c :: tail) = vars :=
        GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons
          (f := c :: tail) (vars := vars) (c := c) (tail := tail)
          htargetVars rfl
      rw [hspecs]
      simp [sameSupportTwoChargeCandidateSpecs, hcandidate]

/--
The permutation-insensitive two-charge recovery succeeds on any nonempty
clause permutation of the direct two-cycle same-support component.
-/
theorem recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_twoCycle
    {target : CNFModel.CNF
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m}
    (hperm : List.Perm target (TseitinCycleCNFFormula 2 (by decide)))
    (hnonempty : target ≠ []) :
    recoverTwoChargeSameSupportGroupPerm? target =
      some twoCycleSameSupportFallbackDecomposition := by
  unfold recoverTwoChargeSameSupportGroupPerm?
  have hcand :
      sameSupportTwoChargeCandidateSpecs target =
        generatedParitySpecsForCycle 2 (by decide) :=
    sameSupportTwoChargeCandidateSpecs_eq_generated_of_perm_twoCycle
      hperm hnonempty
  have hcover :
      List.Perm
        (generatedParitySpecsCNF
          (sameSupportTwoChargeCandidateSpecs target))
        target := by
    rw [hcand]
    have hdirect :
        generatedParitySpecsCNF (generatedParitySpecsForCycle 2 (by decide)) =
          TseitinCycleCNFFormula 2 (by decide) := by
      simpa [generatedParitySpecsForCycle, TseitinCycleCNFFormula] using
        (generatedParitySpecsCNF_fromEncoding
          (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)
    rw [hdirect]
    exact hperm.symm
  rw [recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm hcover]
  simp [twoCycleSameSupportFallbackDecomposition, hcand]

/-- The ordinary one-block canonical recognizer misses the direct two-cycle CNF. -/
theorem inferCanonicalParityBlock_twoCycle_eq_none :
    inferCanonicalParityBlock (TseitinCycleCNFFormula 2 (by decide)) = none := by
  have hmiss :
      (inferCanonicalParityBlock (TseitinCycleCNFFormula 2 (by decide))).isSome =
        false := by
    decide
  cases h :
      inferCanonicalParityBlock (TseitinCycleCNFFormula 2 (by decide)) with
  | none =>
      rfl
  | some b =>
      have hsome :
          (inferCanonicalParityBlock
            (TseitinCycleCNFFormula 2 (by decide))).isSome = true := by
        simp [h]
      rw [hmiss] at hsome
      cases hsome

/--
Any nonempty clause permutation of the direct two-cycle CNF still groups as one
canonical support component containing the whole permuted CNF.
-/
theorem groupClausesByCanonicalSupport_eq_single_of_perm_twoCycle
    {target : CNFModel.CNF
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m}
    (hperm : List.Perm target (TseitinCycleCNFFormula 2 (by decide)))
    (hnonempty : target ≠ []) :
    groupClausesByCanonicalSupport target =
      [(GroupFrame.canonicalSupportKeyForVars
          (parityCandidateCanonicalSupportFromBlock
            (TseitinCycleCNFFormula 2 (by decide))),
        target)] := by
  let vars :=
    parityCandidateCanonicalSupportFromBlock
      (TseitinCycleCNFFormula 2 (by decide))
  have hnormal : GroupFrame.VarsInCanonicalSupportOrder vars := by
    dsimp [vars]
    unfold GroupFrame.VarsInCanonicalSupportOrder
    decide
  cases htarget : target with
  | nil =>
      exact False.elim (hnonempty htarget)
  | cons c tail =>
      have hpermCons :
          List.Perm (c :: tail)
            (TseitinCycleCNFFormula 2 (by decide)) := by
        simpa [htarget] using hperm
      have htargetVars :
          GroupFrame.CNFClausesHaveCanonicalSupportVars
            (c :: tail) vars := by
        simpa [vars] using
          (GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm
            (f := c :: tail)
            (g := TseitinCycleCNFFormula 2 (by decide))
            hpermCons
            twoCycleCNF_clausesHaveCandidateSupportVars)
      change
        groupClausesByCanonicalSupport (c :: tail) =
          [(GroupFrame.canonicalSupportKeyForVars vars, c :: tail)]
      apply GroupFrame.groupClausesByCanonicalSupport_cons_eq_single_of_same_key
      ·
        have hcvars :
            canonicalClauseSupportVars c = vars :=
          htargetVars c (List.Mem.head tail)
        rw [canonicalClauseSupportKey, GroupFrame.canonicalSupportKeyForVars,
          hcvars, hnormal]
      ·
        intro d hd
        have hdvars :
            canonicalClauseSupportVars d = vars :=
          htargetVars d (List.Mem.tail c hd)
        rw [canonicalClauseSupportKey, GroupFrame.canonicalSupportKeyForVars,
          hdvars, hnormal]

/--
The ordinary one-block canonical recognizer misses every nonempty clause
permutation of the direct two-cycle CNF.
-/
theorem inferCanonicalParityBlock_eq_none_of_perm_twoCycle
    {target : CNFModel.CNF
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m}
    (hperm : List.Perm target (TseitinCycleCNFFormula 2 (by decide)))
    (hnonempty : target ≠ []) :
    inferCanonicalParityBlock target = none := by
  let vars :=
    parityCandidateCanonicalSupportFromBlock
      (TseitinCycleCNFFormula 2 (by decide))
  cases htarget : target with
  | nil =>
      exact False.elim (hnonempty htarget)
  | cons c tail =>
      cases hdirect :
          TseitinCycleCNFFormula 2 (by decide) with
      | nil =>
          have hlen :
              (TseitinCycleCNFFormula 2 (by decide)).length = 16 := by
            decide
          simp [hdirect] at hlen
      | cons cd directTail =>
          have hpermCons :
              List.Perm (c :: tail) (cd :: directTail) := by
            simpa [htarget, hdirect] using hperm
          have htargetVars :
              GroupFrame.CNFClausesHaveCanonicalSupportVars
                (c :: tail) vars := by
            simpa [vars, hdirect] using
              (GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm
                (f := c :: tail)
                (g := TseitinCycleCNFFormula 2 (by decide))
                (by simpa [htarget] using hperm)
                twoCycleCNF_clausesHaveCandidateSupportVars)
          have hdirectVars :
              GroupFrame.CNFClausesHaveCanonicalSupportVars
                (cd :: directTail) vars := by
            simpa [vars, hdirect] using
              twoCycleCNF_clausesHaveCandidateSupportVars
          cases htargetInfer : inferCanonicalParityBlock (c :: tail) with
          | none =>
              simp [htarget, htargetInfer]
          | some b =>
              rcases
                GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons
                  (f := c :: tail)
                  (g := cd :: directTail)
                  (vars := vars)
                  (cf := c)
                  (cg := cd)
                  (ftail := tail)
                  (gtail := directTail)
                  hpermCons.symm
                  htargetVars
                  hdirectVars
                  rfl
                  rfl
                  htargetInfer with
              ⟨bdirect, hdirectInfer, _hspec, _hblockPerm⟩
              have hnoneDirect :
                  inferCanonicalParityBlock (cd :: directTail) = none := by
                simpa [hdirect] using inferCanonicalParityBlock_twoCycle_eq_none
              simp [hnoneDirect] at hdirectInfer

/-- Direct-CNF unguided recovery returns the certified two-cycle fallback. -/
theorem twoCycleSameSupportUnguidedDirectRecovery_eq_some :
    twoCycleSameSupportUnguidedDirectRecovery? =
      some twoCycleSameSupportFallbackDecomposition := by
  unfold twoCycleSameSupportUnguidedDirectRecovery?
  unfold recoverTwoChargeSameSupportGroup?
  have hcand :
      sameSupportTwoChargeCandidateSpecs (TseitinCycleCNFFormula 2 (by decide)) =
        generatedParitySpecsForCycle 2 (by decide) :=
    sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated
  have hcover :
      generatedParitySpecsCNF
          (sameSupportTwoChargeCandidateSpecs
            (TseitinCycleCNFFormula 2 (by decide))) =
        TseitinCycleCNFFormula 2 (by decide) := by
    rw [hcand]
    simpa [generatedParitySpecsForCycle, TseitinCycleCNFFormula] using
      (generatedParitySpecsCNF_fromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge)
  rw [recoverSameSupportGeneratedParitySpecs_eq_some_of_cnf_eq hcover]
  simp [twoCycleSameSupportFallbackDecomposition, hcand]

/--
The exact-list unguided recovery is order-sensitive: reversing the direct
two-cycle CNF defeats the current exact-coverage check.
-/
theorem twoCycleSameSupportUnguidedDirectRecovery_reverse_isSome_false :
    (recoverTwoChargeSameSupportGroup?
      (List.reverse (TseitinCycleCNFFormula 2 (by decide)))).isSome = false := by
  decide

/--
The permutation-insensitive unguided recovery repairs that order-sensitivity:
the same reversed two-cycle CNF is accepted as the certified same-support
fallback component.
-/
theorem twoCycleSameSupportUnguidedPermDirectRecovery_reverse_isSome :
    (recoverTwoChargeSameSupportGroupPerm?
      (List.reverse (TseitinCycleCNFFormula 2 (by decide)))).isSome = true := by
  decide

/--
Unguided same-support recovery applied to the actual canonical support grouping
of the direct two-cycle CNF.
-/
def twoCycleSameSupportUnguidedMergedSupportRecovery? :
    Option (CanonicalFingerprintGF2Decomposition
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m) :=
  recoverSingleMergedSupportGroupTwoCharge? twoCycleCanonicalSupportGroups

/--
The unguided two-charge splitter succeeds on the actual one-group two-cycle
canonical support component.
-/
theorem twoCycleSameSupportUnguidedMergedSupportRecovery_isSome :
    twoCycleSameSupportUnguidedMergedSupportRecovery?.isSome = true := by
  decide

/--
Canonical support splitter with a narrow same-support fallback.  It first uses
the existing one-block canonical recognizer.  If that fails, it tries the
same-support fallback branch on the same group before residualizing the group:
first the legacy two-charge path, then exhaustive bounded charge search.
-/
def splitCanonicalSupportClauseGroupsWithTwoChargeFallback {m : Nat} :
    List (CanonicalSupportClauseGroup m) ->
      CanonicalFingerprintGF2Decomposition m
  | [] =>
      { blocks := []
        residualCNF := [] }
  | g :: groups =>
      let rest := splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups
      match inferCanonicalParityBlock g.2 with
      | some b =>
          { blocks := b :: rest.blocks
            residualCNF := rest.residualCNF }
      | none =>
          match recoverSameSupportGroupWithChargeSearchFallback? g.2 with
          | some d =>
              { blocks := d.blocks ++ rest.blocks
                residualCNF := d.residualCNF ++ rest.residualCNF }
          | none =>
              { blocks := rest.blocks
                residualCNF := g.2 ++ rest.residualCNF }

/--
Full-CNF canonical splitter with the same-support fallback enabled.  The
fallback is production-shaped but still bounded exhaustive search after the
legacy two-charge fast path; this is not an efficiency claim or a completeness
claim for arbitrary same-support components.
-/
def splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback {m : Nat}
    (f : CNFModel.CNF m) : CanonicalFingerprintGF2Decomposition m :=
  splitCanonicalSupportClauseGroupsWithTwoChargeFallback
    (groupClausesByCanonicalSupport f)

/--
The enhanced fallback splitter preserves all ordinary clauses up to
permutation.  Recognized one-block groups move into the core, successful
same-support fallback groups move into the core as a residual-free local
decomposition, and all other groups remain residual.
-/
theorem splitCanonicalSupportClauseGroupsWithTwoChargeFallback_expandedCNF_perm
    {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) :
    List.Perm
      (splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).expandedCNF
      (ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups) := by
  induction groups with
  | nil =>
      simp [splitCanonicalSupportClauseGroupsWithTwoChargeFallback,
        CanonicalFingerprintGF2Decomposition.expandedCNF,
        CanonicalFingerprintGF2Decomposition.coreCNF,
        canonicalFingerprintRecognizedBlocksCNF,
        ExtractorCompleteness.canonicalSupportClauseGroupsCNF]
  | cons g groups ih =>
      unfold splitCanonicalSupportClauseGroupsWithTwoChargeFallback
      cases hinfer : inferCanonicalParityBlock g.2 with
      | some b =>
          have hb : b.blockCNF = g.2 :=
            ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
          simp [hinfer, CanonicalFingerprintGF2Decomposition.expandedCNF,
            CanonicalFingerprintGF2Decomposition.coreCNF,
            canonicalFingerprintRecognizedBlocksCNF,
            ExtractorCompleteness.canonicalSupportClauseGroupsCNF, hb]
          exact List.Perm.append_left g.2 ih
      | none =>
          cases hrec : recoverSameSupportGroupWithChargeSearchFallback? g.2 with
          | some d =>
              have hsound := recoverSameSupportGroupWithChargeSearchFallback_sound hrec
              have hres : d.residualCNF = [] := by
                simpa [CanonicalFingerprintGF2Decomposition.hasEmptyResidual] using
                  hsound.2
              have hdcore :
                  List.Perm (canonicalFingerprintRecognizedBlocksCNF d.blocks) g.2 := by
                simpa [CanonicalFingerprintGF2Decomposition.expandedCNF,
                  CanonicalFingerprintGF2Decomposition.coreCNF,
                  hres] using hsound.1
              have htail :
                  List.Perm
                    (splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).expandedCNF
                    (groups.bind Prod.snd) := by
                simpa [ExtractorCompleteness.canonicalSupportClauseGroupsCNF] using ih
              simp [hinfer, hrec, CanonicalFingerprintGF2Decomposition.expandedCNF,
                CanonicalFingerprintGF2Decomposition.coreCNF,
                canonicalFingerprintRecognizedBlocksCNF_append,
                canonicalFingerprintRecognizedBlocksCNF,
                ExtractorCompleteness.canonicalSupportClauseGroupsCNF,
                hres]
              simpa [canonicalFingerprintRecognizedBlocksCNF] using
                List.Perm.append hdcore htail
          | none =>
              simp [hinfer, hrec, CanonicalFingerprintGF2Decomposition.expandedCNF,
                CanonicalFingerprintGF2Decomposition.coreCNF,
                canonicalFingerprintRecognizedBlocksCNF,
                ExtractorCompleteness.canonicalSupportClauseGroupsCNF]
              have htail :
                  List.Perm
                    (((splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).blocks.bind
                      fun b => b.blockCNF) ++
                        (splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).residualCNF)
                    (groups.bind Prod.snd) := by
                simpa [CanonicalFingerprintGF2Decomposition.expandedCNF,
                  CanonicalFingerprintGF2Decomposition.coreCNF,
                  canonicalFingerprintRecognizedBlocksCNF,
                  ExtractorCompleteness.canonicalSupportClauseGroupsCNF] using ih
              have hswap :
                  List.Perm
                    (((splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).blocks.bind
                      fun b => b.blockCNF) ++
                        (g.2 ++
                          (splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).residualCNF))
                    (g.2 ++
                      (((splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).blocks.bind
                        fun b => b.blockCNF) ++
                          (splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).residualCNF)) := by
                simpa [List.append_assoc] using
                  List.Perm.append_right
                    (splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).residualCNF
                    (List.perm_append_comm :
                      List.Perm
                        (((splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).blocks.bind
                          fun b => b.blockCNF) ++ g.2)
                        (g.2 ++
                          ((splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).blocks.bind
                            fun b => b.blockCNF)))
              have htailLeft :
                  List.Perm
                    (g.2 ++
                      (((splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).blocks.bind
                        fun b => b.blockCNF) ++
                          (splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups).residualCNF))
                    (g.2 ++ groups.bind Prod.snd) :=
                List.Perm.append_left g.2 htail
              exact List.Perm.trans hswap htailLeft

/-- The enhanced full-CNF splitter preserves the input CNF up to permutation. -/
theorem splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_expandedCNF_perm
    {m : Nat} (f : CNFModel.CNF m) :
    List.Perm
      (splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f).expandedCNF
      f := by
  unfold splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
  exact
    List.Perm.trans
      (splitCanonicalSupportClauseGroupsWithTwoChargeFallback_expandedCNF_perm
        (groupClausesByCanonicalSupport f))
      (GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm f)

/--
Residual-free enhanced fallback support-group splits compose across appended
group lists.  This is the fallback-splitter analogue of the baseline
`splitCanonicalSupportClauseGroups_append_of_residual_free` frame lemma.
-/
theorem splitCanonicalSupportClauseGroupsWithTwoChargeFallback_append_of_residual_free
    {m : Nat}
    {leftGroups rightGroups : List (CanonicalSupportClauseGroup m)}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hleft :
      splitCanonicalSupportClauseGroupsWithTwoChargeFallback leftGroups =
        { blocks := leftBlocks, residualCNF := [] })
    (hright :
      splitCanonicalSupportClauseGroupsWithTwoChargeFallback rightGroups =
        { blocks := rightBlocks, residualCNF := [] }) :
    splitCanonicalSupportClauseGroupsWithTwoChargeFallback
        (leftGroups ++ rightGroups) =
      { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } := by
  induction leftGroups generalizing leftBlocks with
  | nil =>
      simp [splitCanonicalSupportClauseGroupsWithTwoChargeFallback] at hleft
      cases hleft
      simpa [splitCanonicalSupportClauseGroupsWithTwoChargeFallback] using hright
  | cons g groups ih =>
      unfold splitCanonicalSupportClauseGroupsWithTwoChargeFallback at hleft
      cases hinfer : inferCanonicalParityBlock g.2 with
      | some b =>
          cases htail :
              splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups with
          | mk tailBlocks tailResidual =>
              simp [hinfer, htail] at hleft
              cases leftBlocks with
              | nil =>
                  simp at hleft
              | cons b' leftBlocksTail =>
                  cases hleft with
                  | intro hblocks hresidual =>
                      cases hblocks
                      cases hresidual
                      have htailFree :
                          splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups =
                            { blocks := tailBlocks, residualCNF := [] } := by
                        simpa using htail
                      have hih := ih htailFree
                      unfold splitCanonicalSupportClauseGroupsWithTwoChargeFallback
                      simp [hinfer, hih]
      | none =>
          cases hrec : recoverSameSupportGroupWithChargeSearchFallback? g.2 with
          | some d =>
              cases htail :
                  splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups with
              | mk tailBlocks tailResidual =>
                  simp [hinfer, hrec, htail] at hleft
                  cases hleft with
                  | intro hblocks hresidual =>
                      have hdres : d.residualCNF = [] := by
                        exact hresidual.1
                      have htailResidual : tailResidual = [] := by
                        exact hresidual.2
                      have htailFree :
                          splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups =
                            { blocks := tailBlocks, residualCNF := [] } := by
                        simpa [htailResidual] using htail
                      have hih := ih htailFree
                      have hblocksAppend :
                          d.blocks ++ (tailBlocks ++ rightBlocks) =
                            leftBlocks ++ rightBlocks := by
                        rw [<- List.append_assoc, hblocks]
                      unfold splitCanonicalSupportClauseGroupsWithTwoChargeFallback
                      simp [hinfer, hrec, hih, hdres, hblocksAppend]
          | none =>
              cases htail :
                  splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups with
              | mk tailBlocks tailResidual =>
                  simp [hinfer, hrec, htail] at hleft
                  cases hleft with
                  | intro hblocks hrest =>
                      cases hrest with
                      | intro hgempty hresidual =>
                          cases hblocks
                          cases hresidual
                          have htailFree :
                              splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups =
                                { blocks := leftBlocks, residualCNF := [] } := by
                            simpa using htail
                          have hih := ih htailFree
                          have hinferEmpty :
                              inferCanonicalParityBlock
                                ([] : CNFModel.CNF m) = none := by
                            simpa [hgempty] using hinfer
                          have hrecEmpty :
                              recoverSameSupportGroupWithChargeSearchFallback?
                                ([] : CNFModel.CNF m) = none := by
                            simpa [hgempty] using hrec
                          unfold splitCanonicalSupportClauseGroupsWithTwoChargeFallback
                          simp [hih, hgempty, hinferEmpty, hrecEmpty]

/--
Exact enhanced fallback splitter frame under operational
canonical-support-key disjointness.  If each fragment is already residual-free
with known emitted blocks, then splitting the append emits exactly the left
blocks followed by the right blocks and leaves no residual CNF.
-/
theorem splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : GroupFrame.CNFClauseKeysDisjoint f g)
    (hleft :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := leftBlocks, residualCNF := [] })
    (hright :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback g =
        { blocks := rightBlocks, residualCNF := [] }) :
    splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback (f ++ g) =
      { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } := by
  unfold splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
    at hleft hright
  unfold splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
  rw [GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
    f g hdisjoint]
  exact
    splitCanonicalSupportClauseGroupsWithTwoChargeFallback_append_of_residual_free
      hleft hright

/--
Exact enhanced fallback splitter frame under ordinary variable-disjoint support,
with the same nonempty-right-CNF side condition required by the grouping frame.
-/
theorem splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_disjointSupport
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := leftBlocks, residualCNF := [] })
    (hright :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback g =
        { blocks := rightBlocks, residualCNF := [] }) :
    splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback (f ++ g) =
      { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } :=
  splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_clauseKeysDisjoint
    (GroupFrame.clauseKeysDisjoint_of_disjointSupport
      f g hdisjoint hnonempty)
    hleft hright

/--
Recognized canonical support groups are also residual-free for the enhanced
fallback splitter.  The fallback branch is not used: every group is accepted by
the ordinary one-block recognizer first.
-/
theorem splitCanonicalSupportClauseGroupsWithTwoChargeFallback_of_groupsRecognized
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (h : ExtractorCompleteness.GroupsRecognized groups blocks) :
    splitCanonicalSupportClauseGroupsWithTwoChargeFallback groups =
      { blocks := blocks, residualCNF := [] } := by
  induction groups generalizing blocks with
  | nil =>
      cases blocks with
      | nil =>
          rfl
      | cons _ _ =>
          cases h
  | cons g groups ih =>
      cases blocks with
      | nil =>
          cases h
      | cons b blocks =>
          have hinfer : inferCanonicalParityBlock g.2 = some b := h.1
          have htail : ExtractorCompleteness.GroupsRecognized groups blocks := h.2
          have hsplit := ih htail
          simp [splitCanonicalSupportClauseGroupsWithTwoChargeFallback,
            hinfer, hsplit]

/-- Enhanced splitter output on the direct two-cycle same-support boundary. -/
def twoCycleSameSupportTwoChargeFallbackSplitter :
    CanonicalFingerprintGF2Decomposition
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m :=
  splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
    (TseitinCycleCNFFormula 2 (by decide))

/--
The two-charge fallback splitter covers the direct two-cycle CNF exactly under
the residual-carrying decomposition interface.
-/
theorem twoCycleSameSupportTwoChargeFallbackSplitter_expandedCNF_eq :
    twoCycleSameSupportTwoChargeFallbackSplitter.expandedCNF =
      TseitinCycleCNFFormula 2 (by decide) := by
  decide

/--
The two-charge fallback splitter compacts the direct two-cycle CNF to the
direct two-equation GF(2) target.
-/
theorem twoCycleSameSupportTwoChargeFallbackSplitter_coreGF2_eq :
    twoCycleSameSupportTwoChargeFallbackSplitter.coreGF2 =
      TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge := by
  rfl

/-- The enhanced two-cycle splitter leaves no residual clauses. -/
theorem twoCycleSameSupportTwoChargeFallbackSplitter_hasEmptyResidual :
    twoCycleSameSupportTwoChargeFallbackSplitter.hasEmptyResidual := by
  rfl

/-- The enhanced two-cycle splitter emits exactly two compact equations. -/
theorem twoCycleSameSupportTwoChargeFallbackSplitter_coreEquationCount :
    twoCycleSameSupportTwoChargeFallbackSplitter.coreEquationCount = 2 := by
  decide

/-- The enhanced two-cycle splitter has zero residual ordinary clauses. -/
theorem twoCycleSameSupportTwoChargeFallbackSplitter_residualClauseCount :
    twoCycleSameSupportTwoChargeFallbackSplitter.residualClauseCount = 0 := by
  decide

/--
Enhanced splitter output on the reversed direct two-cycle same-support boundary.
The exact-list fallback used to residualize this input; the production splitter
now uses the permutation-insensitive same-support recovery.
-/
def twoCycleSameSupportTwoChargeFallbackSplitterReversed :
    CanonicalFingerprintGF2Decomposition
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m :=
  splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
    (List.reverse (TseitinCycleCNFFormula 2 (by decide)))

/--
The enhanced splitter preserves the reversed direct two-cycle CNF up to
permutation.
-/
theorem twoCycleSameSupportTwoChargeFallbackSplitterReversed_expandedCNF_perm :
    List.Perm
      twoCycleSameSupportTwoChargeFallbackSplitterReversed.expandedCNF
      (List.reverse (TseitinCycleCNFFormula 2 (by decide))) :=
  splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_expandedCNF_perm
    (List.reverse (TseitinCycleCNFFormula 2 (by decide)))

/--
The enhanced splitter compacts the reversed direct two-cycle CNF to the same
direct two-equation GF(2) target.
-/
theorem twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreGF2_eq :
    twoCycleSameSupportTwoChargeFallbackSplitterReversed.coreGF2 =
      TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge := by
  rfl

/--
The enhanced splitter now leaves no residual clauses on the reversed direct
two-cycle CNF.
-/
theorem twoCycleSameSupportTwoChargeFallbackSplitterReversed_hasEmptyResidual :
    twoCycleSameSupportTwoChargeFallbackSplitterReversed.hasEmptyResidual := by
  rfl

/--
The enhanced splitter still emits exactly two compact equations on the reversed
direct two-cycle CNF.
-/
theorem twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreEquationCount :
    twoCycleSameSupportTwoChargeFallbackSplitterReversed.coreEquationCount = 2 := by
  decide

/--
The enhanced splitter has zero residual ordinary clauses on the reversed direct
two-cycle CNF.
-/
theorem twoCycleSameSupportTwoChargeFallbackSplitterReversed_residualClauseCount :
    twoCycleSameSupportTwoChargeFallbackSplitterReversed.residualClauseCount = 0 := by
  decide

/-- Accepted syntactic signals supply the per-block permutation certificates. -/
theorem CanonicalBlocksPermCertified.of_syntacticSignals
    {m : Nat} {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (h : CanonicalBlocksSyntacticSignals blocks) :
    CanonicalBlocksPermCertified blocks := by
  induction blocks with
  | nil => exact True.intro
  | cons _b _blocks ih =>
      exact And.intro
        (by
          simpa [ParityBlockSyntacticSpec.expandedCNF] using
            parityBlockRecognitionSignal_sound h.1)
        (ih h.2)

/--
Canonical-fingerprint recognized block lists form a declarative parity-encoded
class once each atom carries literal-level permutation evidence and the block
sequence is support-disjoint in append order.
-/
theorem class_of_canonicalFingerprintRecognizedBlocks_permCertified
    {m : Nat} {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : CanonicalBlocksPermCertified blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ParityEncoded.Class m
      (canonicalFingerprintRecognizedBlocksCNF blocks)
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  induction blocks with
  | nil =>
      exact ParityEncoded.Class.empty
  | cons b blocks ih =>
      have hb :
          ParityEncoded.Class m b.blockCNF [b.compactGF2] :=
        class_of_canonicalFingerprintRecognizedBlock_perm b hperm.1
      have htail :
          ParityEncoded.Class m
            (canonicalFingerprintRecognizedBlocksCNF blocks)
            (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
        ih hperm.2 hdisjoint.2
      simpa [canonicalFingerprintRecognizedBlocksCNF,
        canonicalFingerprintRecognizedBlocksGF2] using
        ParityEncoded.Class.union hb htail hdisjoint.1

/--
Syntactically accepted canonical blocks form a declarative class when their
sequence is append-disjoint.
-/
theorem class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals
    {m : Nat} {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ParityEncoded.Class m
      (canonicalFingerprintRecognizedBlocksCNF blocks)
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact class_of_canonicalFingerprintRecognizedBlocks_permCertified
    (CanonicalBlocksPermCertified.of_syntacticSignals hsyntactic)
    hdisjoint

/--
Canonical-fingerprint recognized block lists form a declarative parity-encoded
class without any support-disjointness premise when composed through the
semantic append/gluing constructor.
-/
theorem class_of_canonicalFingerprintRecognizedBlocks_permCertified_append
    {m : Nat} {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : CanonicalBlocksPermCertified blocks) :
    ParityEncoded.Class m
      (canonicalFingerprintRecognizedBlocksCNF blocks)
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  induction blocks with
  | nil =>
      exact ParityEncoded.Class.empty
  | cons b blocks ih =>
      have hb :
          ParityEncoded.Class m b.blockCNF [b.compactGF2] :=
        class_of_canonicalFingerprintRecognizedBlock_perm b hperm.1
      have htail :
          ParityEncoded.Class m
            (canonicalFingerprintRecognizedBlocksCNF blocks)
            (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
        ih hperm.2
      simpa [canonicalFingerprintRecognizedBlocksCNF,
        canonicalFingerprintRecognizedBlocksGF2] using
        ParityEncoded.Class.append hb htail

/--
Syntactically accepted canonical blocks form a declarative class through
semantic append/gluing. This is the class lane for overlapping parity blocks;
support-disjointness is only needed by frame lemmas, not by semantic soundness.
-/
theorem class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
    {m : Nat} {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks) :
    ParityEncoded.Class m
      (canonicalFingerprintRecognizedBlocksCNF blocks)
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact class_of_canonicalFingerprintRecognizedBlocks_permCertified_append
    (CanonicalBlocksPermCertified.of_syntacticSignals hsyntactic)

/--
Any successful guided generated-spec same-support recovery is semantically
sound as a local CNF-to-GF(2) block.  This uses the recovery's exact coverage
and residual-free guarantees to transport the generated-block class witness
back to the recovered component.
-/
theorem class_of_recoverSameSupportGeneratedParitySpecs
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGeneratedParitySpecs? groupCNF specs = some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  have hsyntactic :
      CanonicalBlocksToSyntacticOk d.blocks :=
    recoverSameSupportGeneratedParitySpecs_toSyntacticOk hrec
  have hclassCore :
      ParityEncoded.Class m d.coreCNF d.coreGF2 :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
  have hsound := recoverSameSupportGeneratedParitySpecs_sound hrec
  have hres : d.residualCNF = [] := hsound.2.1
  have hcore : d.coreCNF = groupCNF := by
    simpa [CanonicalFingerprintGF2Decomposition.expandedCNF, hres] using
      hsound.1
  simpa [hcore] using hclassCore

/--
Any successful permutation-insensitive guided generated-spec same-support
recovery is semantically sound as a local CNF-to-GF(2) block.
-/
theorem class_of_recoverSameSupportGeneratedParitySpecsPerm
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGeneratedParitySpecsPerm? groupCNF specs = some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  have hsyntactic :
      CanonicalBlocksToSyntacticOk d.blocks :=
    recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk hrec
  have hclassCore :
      ParityEncoded.Class m d.coreCNF d.coreGF2 :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
  have hsound := recoverSameSupportGeneratedParitySpecsPerm_sound hrec
  have hres : d.residualCNF = [] := hsound.2.1
  have hcorePerm : List.Perm d.coreCNF groupCNF := by
    simpa [CanonicalFingerprintGF2Decomposition.expandedCNF, hres] using
      hsound.1
  exact ParityEncoded.Class.cnf_perm hcorePerm hclassCore

/--
Any successful support-inferred, charge-guided same-support recovery is
semantically sound as a local CNF-to-GF(2) block.
-/
theorem class_of_recoverSameSupportGeneratedParityChargesPerm
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {charges : List Bool}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGeneratedParityChargesPerm? groupCNF charges = some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  unfold recoverSameSupportGeneratedParityChargesPerm? at hrec
  exact class_of_recoverSameSupportGeneratedParitySpecsPerm hrec

/--
Any successful unguided two-charge same-support recovery is semantically sound
as a local CNF-to-GF(2) block.
-/
theorem class_of_recoverTwoChargeSameSupportGroup
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroup? groupCNF = some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  have hsyntactic :
      CanonicalBlocksToSyntacticOk d.blocks :=
    recoverTwoChargeSameSupportGroup_toSyntacticOk hrec
  have hclassCore :
      ParityEncoded.Class m d.coreCNF d.coreGF2 :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
  have hsound := recoverTwoChargeSameSupportGroup_sound hrec
  have hres : d.residualCNF = [] := hsound.2
  have hcore : d.coreCNF = groupCNF := by
    simpa [CanonicalFingerprintGF2Decomposition.expandedCNF, hres] using
      hsound.1
  simpa [hcore] using hclassCore

/--
Any successful permutation-insensitive unguided two-charge same-support
recovery is semantically sound as a local CNF-to-GF(2) block.  The local
decomposition only covers the source component up to clause permutation, so the
semantic class transports across the CNF permutation witness.
-/
theorem class_of_recoverTwoChargeSameSupportGroupPerm
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroupPerm? groupCNF = some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  have hsyntactic :
      CanonicalBlocksToSyntacticOk d.blocks :=
    recoverTwoChargeSameSupportGroupPerm_toSyntacticOk hrec
  have hclassCore :
      ParityEncoded.Class m d.coreCNF d.coreGF2 :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
  have hsound := recoverTwoChargeSameSupportGroupPerm_sound hrec
  have hres : d.residualCNF = [] := hsound.2
  have hcorePerm : List.Perm d.coreCNF groupCNF := by
    simpa [CanonicalFingerprintGF2Decomposition.expandedCNF, hres] using
      hsound.1
  exact ParityEncoded.Class.cnf_perm hcorePerm hclassCore

/--
A successful residual-free local decomposition whose emitted canonical blocks
upgrade to syntactic parity blocks yields a declarative semantic class witness.
-/
theorem class_of_decomposition_cover_toSyntacticOk
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hcover : List.Perm d.expandedCNF groupCNF)
    (hresidual : d.hasEmptyResidual)
    (hsyntactic : CanonicalBlocksToSyntacticOk d.blocks) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  have hclassCore :
      ParityEncoded.Class m d.coreCNF d.coreGF2 :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
  have hres : d.residualCNF = [] := by
    simpa [CanonicalFingerprintGF2Decomposition.hasEmptyResidual] using
      hresidual
  have hcorePerm : List.Perm d.coreCNF groupCNF := by
    simpa [CanonicalFingerprintGF2Decomposition.expandedCNF, hres] using
      hcover
  exact ParityEncoded.Class.cnf_perm hcorePerm hclassCore

/--
Successful unguided same-support recovery from a single merged support group
returns a local semantic class witness for that group's CNF component.
-/
theorem class_of_recoverSingleMergedSupportGroupTwoCharge
    {m : Nat} {groups : List (CanonicalSupportClauseGroup m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSingleMergedSupportGroupTwoCharge? groups = some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ ParityEncoded.Class m g.2 d.coreGF2 := by
  rcases recoverSingleMergedSupportGroupTwoCharge_sound hrec with
    ⟨g, hgroups, hcover, hresidual⟩
  refine ⟨g, hgroups, ?_⟩
  have hclassCore :
      ParityEncoded.Class m d.coreCNF d.coreGF2 :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk
        (recoverSingleMergedSupportGroupTwoCharge_toSyntacticOk hrec))
  have hres : d.residualCNF = [] := hresidual
  have hcore : d.coreCNF = g.2 := by
    simpa [CanonicalFingerprintGF2Decomposition.expandedCNF, hres] using hcover
  simpa [hcore] using hclassCore

/--
Successful permutation-insensitive guided recovery from a supplied generated
same-support split returns a local semantic class witness for that group's CNF
component.
-/
theorem class_of_recoverSingleMergedSupportGroupFromGeneratedSpecsPerm
    {m : Nat} {groups : List (CanonicalSupportClauseGroup m)}
    {specs : List (GeneratedParitySpec m)}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromGeneratedSpecsPerm? groups specs = some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ ParityEncoded.Class m g.2 d.coreGF2 := by
  rcases recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_sound hrec with
    ⟨g, hgroups, _hcover, _hresidual, _hgf2⟩
  refine ⟨g, hgroups, ?_⟩
  exact class_of_recoverSameSupportGeneratedParitySpecsPerm
    (by
      subst groups
      simpa [recoverSingleMergedSupportGroupFromGeneratedSpecsPerm?] using hrec)

/--
Successful support-inferred, charge-guided recovery from one merged support
group returns a local semantic class witness for that group's CNF component.
-/
theorem class_of_recoverSingleMergedSupportGroupFromChargesPerm
    {m : Nat} {groups : List (CanonicalSupportClauseGroup m)}
    {charges : List Bool}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromChargesPerm? groups charges = some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ ParityEncoded.Class m g.2 d.coreGF2 := by
  rcases recoverSingleMergedSupportGroupFromChargesPerm_sound hrec with
    ⟨g, hgroups, _hcover, _hresidual, _hgf2⟩
  refine ⟨g, hgroups, ?_⟩
  exact class_of_recoverSameSupportGeneratedParityChargesPerm
    (by
      subst groups
      simpa [recoverSingleMergedSupportGroupFromChargesPerm?] using hrec)

/--
Any successful bounded charge-search recovery is semantically sound as a local
CNF-to-GF(2) block.
-/
theorem class_of_recoverSameSupportGeneratedParityChargeSearchPerm
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {maxCharges : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGeneratedParityChargeSearchPerm? groupCNF maxCharges =
        some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  unfold recoverSameSupportGeneratedParityChargeSearchPerm? at hrec
  rcases firstSome?_eq_some_imp_exists_mem hrec with
    ⟨charges, _hmem, hchargeRec⟩
  exact class_of_recoverSameSupportGeneratedParityChargesPerm hchargeRec

/--
Successful bounded charge-search recovery from one merged support group returns
a local semantic class witness for that group's CNF component.
-/
theorem class_of_recoverSingleMergedSupportGroupFromChargeSearchPerm
    {m : Nat} {groups : List (CanonicalSupportClauseGroup m)}
    {maxCharges : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSingleMergedSupportGroupFromChargeSearchPerm? groups maxCharges =
        some d) :
    exists g : CanonicalSupportClauseGroup m,
      groups = [g] /\ ParityEncoded.Class m g.2 d.coreGF2 := by
  rcases recoverSingleMergedSupportGroupFromChargeSearchPerm_sound hrec with
    ⟨g, _charges, hgroups, _hmem, _hcover, _hresidual, _hgf2⟩
  refine ⟨g, hgroups, ?_⟩
  exact class_of_recoverSameSupportGeneratedParityChargeSearchPerm
    (by
      subst groups
      simpa [recoverSingleMergedSupportGroupFromChargeSearchPerm?] using hrec)

/--
Any successful arity-three/four direct same-support fallback is semantically
sound as a local CNF-to-GF(2) block.
-/
theorem class_of_recoverSameSupportGroupWithDirectChargeFallback
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGroupWithDirectChargeFallback? groupCNF = some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  rcases recoverSameSupportGroupWithDirectChargeFallback_sound hrec with
    ⟨hcover, hresidual⟩
  exact
    class_of_decomposition_cover_toSyntacticOk hcover hresidual
      (recoverSameSupportGroupWithDirectChargeFallback_toSyntacticOk hrec)

/--
Any successful block-size-parameterized same-support fallback is semantically
sound as a local CNF-to-GF(2) block.
-/
theorem class_of_recoverSameSupportGroupWithDirectBlockSizeFallback
    {m : Nat} {groupCNF : CNFModel.CNF m} {blockSize : Nat}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGroupWithDirectBlockSizeFallback? groupCNF blockSize =
        some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  rcases recoverSameSupportGroupWithDirectBlockSizeFallback_sound hrec with
    ⟨hcover, hresidual⟩
  exact
    class_of_decomposition_cover_toSyntacticOk hcover hresidual
      (recoverSameSupportGroupWithDirectBlockSizeFallback_toSyntacticOk hrec)

/--
Any successful support-size-inferred same-support fallback is semantically
sound as a local CNF-to-GF(2) block.
-/
theorem class_of_recoverSameSupportGroupWithDirectInferredBlockSizeFallback
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec :
      recoverSameSupportGroupWithDirectInferredBlockSizeFallback? groupCNF =
        some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  rcases recoverSameSupportGroupWithDirectInferredBlockSizeFallback_sound hrec with
    ⟨hcover, hresidual⟩
  exact
    class_of_decomposition_cover_toSyntacticOk hcover hresidual
      (recoverSameSupportGroupWithDirectInferredBlockSizeFallback_toSyntacticOk
        hrec)

/--
Any successful production-shaped same-support fallback is semantically sound as
a local CNF-to-GF(2) block.
-/
theorem class_of_recoverSameSupportGroupWithChargeSearchFallback
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGroupWithChargeSearchFallback? groupCNF = some d) :
    ParityEncoded.Class m groupCNF d.coreGF2 := by
  rcases recoverSameSupportGroupWithChargeSearchFallback_sound hrec with
    ⟨hcover, hresidual⟩
  exact
    class_of_decomposition_cover_toSyntacticOk hcover hresidual
      (recoverSameSupportGroupWithChargeSearchFallback_toSyntacticOk hrec)

/-- Per-assignment semantic preservation for a successful two-charge recovery. -/
theorem semanticPreservation_of_recoverTwoChargeSameSupportGroup
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroup? groupCNF = some d)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a groupCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 :=
  ParityEncoded.Class.sound
    (class_of_recoverTwoChargeSameSupportGroup hrec) a

/--
Per-assignment semantic preservation for a successful permutation-insensitive
two-charge recovery.
-/
theorem semanticPreservation_of_recoverTwoChargeSameSupportGroupPerm
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverTwoChargeSameSupportGroupPerm? groupCNF = some d)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a groupCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 :=
  ParityEncoded.Class.sound
    (class_of_recoverTwoChargeSameSupportGroupPerm hrec) a

/--
Per-assignment semantic preservation for a successful production-shaped
same-support fallback.
-/
theorem semanticPreservation_of_recoverSameSupportGroupWithChargeSearchFallback
    {m : Nat} {groupCNF : CNFModel.CNF m}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hrec : recoverSameSupportGroupWithChargeSearchFallback? groupCNF = some d)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a groupCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 :=
  ParityEncoded.Class.sound
    (class_of_recoverSameSupportGroupWithChargeSearchFallback hrec) a

/--
When the support groups for a CNF are all recognized, the emitted canonical
blocks cover exactly the original CNF up to clause permutation.
-/
theorem canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized
    {m : Nat}
    {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks) :
    List.Perm (canonicalFingerprintRecognizedBlocksCNF blocks) f := by
  have hsplit :
      splitCanonicalSupportClauseGroups groups =
        { blocks := blocks, residualCNF := [] } :=
    ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
      hrec
  have hcover :
      List.Perm
        (splitCanonicalSupportClauseGroups groups).expandedCNF
        (ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups) :=
    ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm
      groups
  have hgroupCover :
      List.Perm
        (ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups)
        f := by
    rw [hgroups.symm]
    exact
      GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm
        f
  have hblocks :
      List.Perm
        (canonicalFingerprintRecognizedBlocksCNF blocks)
        (ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups) := by
    simpa [hsplit, CanonicalFingerprintGF2Decomposition.expandedCNF,
      CanonicalFingerprintGF2Decomposition.coreCNF,
      canonicalFingerprintRecognizedBlocksCNF] using hcover
  exact List.Perm.trans hblocks hgroupCover

/--
A residual-free executable canonical split yields a declarative
`ParityEncoded.Class` witness for the original input once the emitted blocks
carry the stronger syntactic recognition signals and append-disjointness.

This is the bridge from the executable splitter back to the declarative class:
grouping and splitting are covered up to clause permutation, while per-block
syntactic signals discharge the atom-level permutation evidence.
-/
theorem class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  have hblocksClass :
      ParityEncoded.Class m
        (canonicalFingerprintRecognizedBlocksCNF blocks)
        (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals
      hsyntactic hdisjoint
  have hsplitCover :
      List.Perm
        (splitArityFourParityCanonicalSupportGroups f).expandedCNF
        f := by
    unfold splitArityFourParityCanonicalSupportGroups
    exact
      List.Perm.trans
        (ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm
          (groupClausesByCanonicalSupport f))
        (GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm
          f)
  have hcovered :
      List.Perm (canonicalFingerprintRecognizedBlocksCNF blocks) f := by
    simpa [hsplit, CanonicalFingerprintGF2Decomposition.expandedCNF,
      CanonicalFingerprintGF2Decomposition.coreCNF,
      canonicalFingerprintRecognizedBlocksCNF] using hsplitCover
  exact ParityEncoded.Class.cnf_perm hcovered hblocksClass

/--
Same split-to-class bridge, with the syntactic-signal premise discharged by the
executable `toSyntactic?` check on every emitted canonical block.
-/
theorem class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals
      hsplit
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
      hdisjoint

/--
A residual-free executable canonical split yields a declarative
`ParityEncoded.Class` witness through semantic append/gluing.  Unlike the
frame-oriented split bridge above, this theorem does not require emitted blocks
to be support-disjoint.
-/
theorem class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  have hblocksClass :
      ParityEncoded.Class m
        (canonicalFingerprintRecognizedBlocksCNF blocks)
        (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      hsyntactic
  have hsplitCover :
      List.Perm
        (splitArityFourParityCanonicalSupportGroups f).expandedCNF
        f := by
    unfold splitArityFourParityCanonicalSupportGroups
    exact
      List.Perm.trans
        (ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm
          (groupClausesByCanonicalSupport f))
        (GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm
          f)
  have hcovered :
      List.Perm (canonicalFingerprintRecognizedBlocksCNF blocks) f := by
    simpa [hsplit, CanonicalFingerprintGF2Decomposition.expandedCNF,
      CanonicalFingerprintGF2Decomposition.coreCNF,
      canonicalFingerprintRecognizedBlocksCNF] using hsplitCover
  exact ParityEncoded.Class.cnf_perm hcovered hblocksClass

/--
The relaxed split-to-class bridge with syntactic recognition signals discharged
by successful executable `toSyntactic?` checks on every emitted canonical block.
-/
theorem class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append
      hsplit
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)

/--
A residual-free enhanced fallback split yields a declarative
`ParityEncoded.Class` witness through semantic append/gluing.  This is the
soundness-facing bridge for the production-shaped two-charge fallback splitter;
it does not claim the splitter is residual-free on arbitrary inputs.
-/
theorem class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_syntacticSignals_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  have hblocksClass :
      ParityEncoded.Class m
        (canonicalFingerprintRecognizedBlocksCNF blocks)
        (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      hsyntactic
  have hsplitCover :
      List.Perm
        (splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f).expandedCNF
        f :=
    splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_expandedCNF_perm
      f
  have hcovered :
      List.Perm (canonicalFingerprintRecognizedBlocksCNF blocks) f := by
    simpa [hsplit, CanonicalFingerprintGF2Decomposition.expandedCNF,
      CanonicalFingerprintGF2Decomposition.coreCNF,
      canonicalFingerprintRecognizedBlocksCNF] using hsplitCover
  exact ParityEncoded.Class.cnf_perm hcovered hblocksClass

/--
The enhanced fallback split-to-class bridge with syntactic recognition signals
discharged by successful executable `toSyntactic?` checks.
-/
theorem class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_syntacticSignals_append
      hsplit
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)

/--
Residual-free enhanced fallback splits preserve CNF/GF(2) semantics when every
emitted block passes the executable syntactic check.  This is intentionally a
semantic theorem, not the older `ExtractorCompleteOn` package, whose API is
tied to the baseline splitter.
-/
theorem semanticPreservation_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a f <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a
        (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
  ParityEncoded.Class.sound
    (class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append
      hsplit hsyntactic) a

/--
Enhanced fallback extractor-completeness package.  This mirrors the baseline
`ExtractorCompleteness.ExtractorCompleteOn` shape, but it is intentionally tied
to `splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback`.
-/
def EnhancedExtractorCompleteOn {m : Nat}
    (f : CNFModel.CNF m) (s : ParityEncoded.GF2Formula m) : Prop :=
  exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
    splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
      { blocks := blocks, residualCNF := [] } /\
    List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s

/--
Combined semantic/enhanced-executable extraction claim for the fallback
splitter.  This is the enhanced analogue of
`ExtractorCompleteness.SemanticExtractorCompleteOn`.
-/
def EnhancedSemanticExtractorCompleteOn {m : Nat}
    (f : CNFModel.CNF m) (s : ParityEncoded.GF2Formula m) : Prop :=
  (forall a : CNFModel.Assignment m,
    CNFModel.cnfSat a f <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a s) /\
    EnhancedExtractorCompleteOn f s

/-- A residual-free enhanced fallback split gives enhanced extractor completeness. -/
theorem enhancedExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {s : ParityEncoded.GF2Formula m}
    (hsplit :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := blocks, residualCNF := [] })
    (hgf2 : List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s) :
    EnhancedExtractorCompleteOn f s := by
  exact Exists.intro blocks (And.intro hsplit hgf2)

/--
Recognized canonical support groups give enhanced fallback extractor
completeness.  This records that the fallback splitter subsumes the baseline
recognized-group lane without invoking any same-support fallback recovery.
-/
theorem enhancedExtractorCompleteOn_of_groupRecognition
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hgf2 : List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s) :
    EnhancedExtractorCompleteOn f s := by
  refine Exists.intro blocks ?_
  constructor
  case left =>
    unfold splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
    rw [hgroups]
    exact
      splitCanonicalSupportClauseGroupsWithTwoChargeFallback_of_groupsRecognized
        hrec
  case right =>
    exact hgf2

/--
Enhanced fallback extractor completeness composes when the grouping pass frames
an append as the concatenation of the two fragment groupings.
-/
theorem enhancedExtractorCompleteOn_append_of_groupAppend
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++ groupClausesByCanonicalSupport g)
    (hleft : EnhancedExtractorCompleteOn f s)
    (hright : EnhancedExtractorCompleteOn g t) :
    EnhancedExtractorCompleteOn (f ++ g) (List.append s t) := by
  cases hleft with
  | intro leftBlocks hleftRest =>
      cases hleftRest with
      | intro hleftSplit hleftGF2 =>
          cases hright with
          | intro rightBlocks hrightRest =>
              cases hrightRest with
              | intro hrightSplit hrightGF2 =>
                  refine Exists.intro (leftBlocks ++ rightBlocks) ?_
                  constructor
                  case left =>
                    unfold splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
                      at hleftSplit hrightSplit
                    unfold splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
                    rw [hgroups]
                    exact
                      splitCanonicalSupportClauseGroupsWithTwoChargeFallback_append_of_residual_free
                        hleftSplit hrightSplit
                  case right =>
                    rw [canonicalFingerprintRecognizedBlocksGF2_append]
                    exact hleftGF2.append hrightGF2

/--
Enhanced fallback extractor completeness composes under operational
canonical-support-key disjointness.
-/
theorem enhancedExtractorCompleteOn_append_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : GroupFrame.CNFClauseKeysDisjoint f g)
    (hleft : EnhancedExtractorCompleteOn f s)
    (hright : EnhancedExtractorCompleteOn g t) :
    EnhancedExtractorCompleteOn (f ++ g) (List.append s t) :=
  enhancedExtractorCompleteOn_append_of_groupAppend
    (GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
      f g hdisjoint)
    hleft hright

/--
Enhanced fallback extractor completeness composes under ordinary
variable-disjoint support when the right-hand CNF has no empty-support clauses.
-/
theorem enhancedExtractorCompleteOn_append_of_disjointSupport
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft : EnhancedExtractorCompleteOn f s)
    (hright : EnhancedExtractorCompleteOn g t) :
    EnhancedExtractorCompleteOn (f ++ g) (List.append s t) :=
  enhancedExtractorCompleteOn_append_of_clauseKeysDisjoint
    (GroupFrame.clauseKeysDisjoint_of_disjointSupport
      f g hdisjoint hnonempty)
    hleft hright

/--
A declarative class witness plus enhanced extractor completeness gives the
combined semantic/enhanced-executable claim.
-/
theorem enhancedSemanticExtractorCompleteOn_of_class
    {m : Nat} {f : CNFModel.CNF m} {s : ParityEncoded.GF2Formula m}
    (hclass : ParityEncoded.Class m f s)
    (hextract : EnhancedExtractorCompleteOn f s) :
    EnhancedSemanticExtractorCompleteOn f s :=
  And.intro (ParityEncoded.Class.sound hclass) hextract

/--
Generated key-disjoint spec lists are residual-free for the enhanced fallback
splitter.  The fallback branch is not needed here: the theorem records that the
enhanced production splitter subsumes the ordinary recognized-group lane.
-/
theorem enhancedExtractorCompleteOn_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    EnhancedExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) := by
  cases groupsRecognized_exists_of_generatedKeyDisjointSpecList hspecs with
  | intro blocks hblocks =>
      exact
        enhancedExtractorCompleteOn_of_groupRecognition
          (f := generatedParitySpecsCNF specs)
          (s := generatedParitySpecsGF2 specs)
          (groups := groupClausesByCanonicalSupport
            (generatedParitySpecsCNF specs))
          (blocks := blocks)
          rfl hblocks.1 hblocks.2

/--
Generated spec lists with fresh canonical support keys are residual-free for
the enhanced fallback splitter.
-/
theorem enhancedExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    EnhancedExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  enhancedExtractorCompleteOn_of_generatedKeyDisjointSpecList
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Generated key-disjoint spec lists satisfy the combined semantic/enhanced
extraction claim for their folded CNF/GF(2) expansions.
-/
theorem enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    EnhancedSemanticExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  enhancedSemanticExtractorCompleteOn_of_class
    (class_of_generatedKeyDisjointSpecList hspecs)
    (enhancedExtractorCompleteOn_of_generatedKeyDisjointSpecList hspecs)

/--
Generated spec lists with fresh canonical support keys satisfy the combined
semantic/enhanced extraction claim.
-/
theorem enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    EnhancedSemanticExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Concrete graph encodings whose generated incident specs are key-disjoint are
residual-free for the enhanced fallback splitter.
-/
theorem enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    EnhancedExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  rw [(generatedParitySpecsCNF_fromEncoding enc charge).symm,
    (generatedParitySpecsGF2_fromEncoding enc charge).symm]
  exact enhancedExtractorCompleteOn_of_generatedKeyDisjointSpecList hspecs

/--
Concrete graph encodings whose generated incident specs have fresh canonical
support keys are residual-free for the enhanced fallback splitter.
-/
theorem enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    EnhancedExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    enc charge (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Concrete graph encodings whose generated incident specs are key-disjoint
satisfy the combined semantic/enhanced extraction claim.
-/
theorem enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  enhancedSemanticExtractorCompleteOn_of_class
    (class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
      enc charge hspecs)
    (enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
      enc charge hspecs)

/--
Concrete graph encodings whose generated incident specs have fresh canonical
support keys satisfy the combined semantic/enhanced extraction claim.
-/
theorem enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
    enc charge (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Cycle-family enhanced extractor completeness reduces to the concrete
key-disjoint side-condition for the generated incident-spec list.
-/
theorem enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    EnhancedExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  dsimp [TseitinCycleCNFFormula, generatedParitySpecsForCycle]
  exact
    enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList
      (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge hspecs

/--
Cycle-family enhanced extractor completeness also reduces to the cleaner
spec-level canonical-key freshness certificate.
-/
theorem enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    EnhancedExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    n hn (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Nondegenerate derived cycles are residual-free for the enhanced fallback
splitter through the ordinary recognized-group path.
-/
theorem enhancedExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate
    (n : Nat) (hn : 1 < n) (hn2 : 2 < n) :
    EnhancedExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    n hn (generatedCanonicalKeyFreshSpecList_forCycle n hn hn2)

/--
Cycle-family combined semantic/enhanced extraction reduces to the concrete
key-disjoint side-condition for the generated incident-spec list.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  enhancedSemanticExtractorCompleteOn_of_class
    (class_of_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
      n hn hspecs)
    (enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
      n hn hspecs)

/--
Cycle-family combined semantic/enhanced extraction also reduces to the cleaner
spec-level canonical-key freshness certificate.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList
    n hn (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Nondegenerate derived cycles satisfy the combined semantic/enhanced extraction
claim through the ordinary recognized-group path of the enhanced splitter.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate
    (n : Nat) (hn : 1 < n) (hn2 : 2 < n) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList
    n hn (generatedCanonicalKeyFreshSpecList_forCycle n hn hn2)

/--
Combined semantic/enhanced-executable extraction composes when the grouping
pass frames an append as the concatenation of the two fragment groupings.
-/
theorem enhancedSemanticExtractorCompleteOn_append_of_groupAppend
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++ groupClausesByCanonicalSupport g)
    (hleft : EnhancedSemanticExtractorCompleteOn f s)
    (hright : EnhancedSemanticExtractorCompleteOn g t) :
    EnhancedSemanticExtractorCompleteOn (f ++ g) (List.append s t) := by
  constructor
  case left =>
    intro a
    constructor
    case mp =>
      intro hsat
      have hsplit := (cnfSat_append_iff a f g).1 hsat
      exact
        (ParityEncoded.gf2Sat_append_iff a s t).2
          (And.intro
            ((hleft.1 a).1 hsplit.1)
            ((hright.1 a).1 hsplit.2))
    case mpr =>
      intro hsat
      have hsplit := (ParityEncoded.gf2Sat_append_iff a s t).1 hsat
      exact
        (cnfSat_append_iff a f g).2
          (And.intro
            ((hleft.1 a).2 hsplit.1)
            ((hright.1 a).2 hsplit.2))
  case right =>
    exact enhancedExtractorCompleteOn_append_of_groupAppend
      hgroups hleft.2 hright.2

/--
Combined semantic/enhanced-executable extraction composes under operational
canonical-support-key disjointness.
-/
theorem enhancedSemanticExtractorCompleteOn_append_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : GroupFrame.CNFClauseKeysDisjoint f g)
    (hleft : EnhancedSemanticExtractorCompleteOn f s)
    (hright : EnhancedSemanticExtractorCompleteOn g t) :
    EnhancedSemanticExtractorCompleteOn (f ++ g) (List.append s t) :=
  enhancedSemanticExtractorCompleteOn_append_of_groupAppend
    (GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
      f g hdisjoint)
    hleft hright

/--
Combined semantic/enhanced-executable extraction composes under ordinary
variable-disjoint support when the right-hand CNF has no empty-support clauses.
-/
theorem enhancedSemanticExtractorCompleteOn_append_of_disjointSupport
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft : EnhancedSemanticExtractorCompleteOn f s)
    (hright : EnhancedSemanticExtractorCompleteOn g t) :
    EnhancedSemanticExtractorCompleteOn (f ++ g) (List.append s t) :=
  enhancedSemanticExtractorCompleteOn_append_of_clauseKeysDisjoint
    (GroupFrame.clauseKeysDisjoint_of_disjointSupport
      f g hdisjoint hnonempty)
    hleft hright

/--
Residual-free enhanced fallback splits with syntactically checked blocks satisfy
the combined semantic/enhanced-executable package for their emitted GF(2) core.
-/
theorem enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks) :
    EnhancedSemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
  enhancedSemanticExtractorCompleteOn_of_class
    (class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append
      hsplit hsyntactic)
    (enhancedExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
      hsplit (List.Perm.refl _))

/--
Residual-free enhanced fallback splits with syntactically checked blocks satisfy
the combined semantic/enhanced-executable package for any permutation of their
emitted GF(2) core.
-/
theorem enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {s : ParityEncoded.GF2Formula m}
    (hsplit :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks)
    (hgf2 : List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s) :
    EnhancedSemanticExtractorCompleteOn f s :=
  enhancedSemanticExtractorCompleteOn_of_class
    (ParityEncoded.Class.gf2_perm hgf2
      (class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append
        hsplit hsyntactic))
    (enhancedExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
      hsplit hgf2)

/--
If a CNF groups as one merged support component, the ordinary one-block
recognizer fails, and the two-charge same-support fallback succeeds on that
component, then the enhanced splitter satisfies the combined semantic/executable
package for the recovered compact GF(2) core.
-/
theorem enhancedSemanticExtractorCompleteOn_of_singleGroupTwoChargeFallback
    {m : Nat} {f : CNFModel.CNF m} {key : CanonicalClauseSupportKey}
    {d : CanonicalFingerprintGF2Decomposition m}
    (hgroups : groupClausesByCanonicalSupport f = [(key, f)])
    (hinfer : inferCanonicalParityBlock f = none)
    (hrec : recoverTwoChargeSameSupportGroupPerm? f = some d) :
    EnhancedSemanticExtractorCompleteOn f d.coreGF2 := by
  have hres : d.residualCNF = [] :=
    (recoverTwoChargeSameSupportGroupPerm_sound hrec).2
  have hfallback :
      recoverSameSupportGroupWithChargeSearchFallback? f = some d := by
    simp [recoverSameSupportGroupWithChargeSearchFallback?, hrec]
  have hsplit :
      splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback f =
        { blocks := d.blocks, residualCNF := [] } := by
    unfold splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
    rw [hgroups]
    change
      splitCanonicalSupportClauseGroupsWithTwoChargeFallback [(key, f)] =
        { blocks := d.blocks, residualCNF := [] }
    simp [splitCanonicalSupportClauseGroupsWithTwoChargeFallback,
      hinfer, hfallback, hres]
  have hgf2 :
      List.Perm (canonicalFingerprintRecognizedBlocksGF2 d.blocks) d.coreGF2 := by
    simp [CanonicalFingerprintGF2Decomposition.coreGF2]
  exact
    enhancedSemanticExtractorCompleteOn_of_class
      (class_of_recoverTwoChargeSameSupportGroupPerm hrec)
      (enhancedExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
        hsplit hgf2)

/--
Generic production-path theorem for the two-charge same-support fallback.  If a
nonempty CNF is a clause permutation of the generated true/false parity
expansions over one canonical support, and the ordinary one-block recognizer
misses it, then the enhanced fallback splitter emits the generated two-equation
GF(2) target with no residual clauses.
-/
theorem enhancedSemanticExtractorCompleteOn_of_perm_generatedParitySpecs_two_sameSupport
    {m : Nat} {vars : List (Fin m)} {target : CNFModel.CNF m}
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hperm :
      List.Perm target
        (generatedParitySpecsCNF [(vars, true), (vars, false)]))
    (hnonempty : target ≠ [])
    (hinfer : inferCanonicalParityBlock target = none) :
    EnhancedSemanticExtractorCompleteOn
      target
      (generatedParitySpecsGF2 [(vars, true), (vars, false)]) := by
  have hgroups :
      groupClausesByCanonicalSupport target =
        [(GroupFrame.canonicalSupportKeyForVars vars, target)] :=
    groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_two_sameSupport
      hnormal hperm hnonempty
  have hrec :
      recoverTwoChargeSameSupportGroupPerm? target =
        some (generatedParitySpecsFallbackDecomposition
          [(vars, true), (vars, false)]) :=
    recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_generatedParitySpecs_two_sameSupport
      hnormal hperm hnonempty
  have hmain :
      EnhancedSemanticExtractorCompleteOn
        target
        (generatedParitySpecsFallbackDecomposition
          [(vars, true), (vars, false)]).coreGF2 :=
    enhancedSemanticExtractorCompleteOn_of_singleGroupTwoChargeFallback
      (f := target)
      (key := GroupFrame.canonicalSupportKeyForVars vars)
      (d := generatedParitySpecsFallbackDecomposition
        [(vars, true), (vars, false)])
      hgroups hinfer hrec
  have hcore :
      (generatedParitySpecsFallbackDecomposition
        [(vars, true), (vars, false)]).coreGF2 =
        generatedParitySpecsGF2 [(vars, true), (vars, false)] :=
    generatedParitySpecsFallbackDecomposition_coreGF2_eq
      [(vars, true), (vars, false)]
  simpa [hcore] using hmain

/--
The enhanced fallback splitter satisfies the combined semantic/enhanced-executable
package on the direct two-cycle boundary.  The semantic half comes from the
declarative cycle class; the executable half uses the enhanced splitter's own
residual-free output and compact GF(2) core.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula 2 (by decide))
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge) := by
  refine And.intro ?sem ?extract
  · exact ParityEncoded.Class.sound
      (class_of_TseitinCycleCNFFormula 2 (by decide))
  · refine ⟨twoCycleSameSupportTwoChargeFallbackSplitter.blocks, ?split, ?gf2⟩
    · have hres :
          (splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
            (TseitinCycleCNFFormula 2 (by decide))).residualCNF = [] := by
          simpa [twoCycleSameSupportTwoChargeFallbackSplitter,
            CanonicalFingerprintGF2Decomposition.hasEmptyResidual] using
            twoCycleSameSupportTwoChargeFallbackSplitter_hasEmptyResidual
      change
        splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
            (TseitinCycleCNFFormula 2 (by decide)) =
          { blocks :=
              (splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
                (TseitinCycleCNFFormula 2 (by decide))).blocks,
            residualCNF := [] }
      cases h :
          splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
            (TseitinCycleCNFFormula 2 (by decide)) with
      | mk blocks residualCNF =>
          simp [h] at hres ⊢
          exact hres
    · have hcore :
          canonicalFingerprintRecognizedBlocksGF2
              twoCycleSameSupportTwoChargeFallbackSplitter.blocks =
            TseitinParityFormulaFromEncoding
              (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge := by
        simpa [CanonicalFingerprintGF2Decomposition.coreGF2] using
          twoCycleSameSupportTwoChargeFallbackSplitter_coreGF2_eq
      exact hcore ▸ List.Perm.refl _

/--
The enhanced fallback splitter satisfies the combined semantic/enhanced-executable
package on the reversed direct two-cycle boundary.  This is the production-path
regression theorem for the permutation-insensitive same-support fallback.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_reversed :
    EnhancedSemanticExtractorCompleteOn
      (List.reverse (TseitinCycleCNFFormula 2 (by decide)))
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge) := by
  refine And.intro ?sem ?extract
  · exact ParityEncoded.Class.sound
      (ParityEncoded.Class.cnf_perm
        (List.Perm.symm
          (TseitinCycleCNFFormula 2 (by decide)).reverse_perm)
        (class_of_TseitinCycleCNFFormula 2 (by decide)))
  · refine ⟨twoCycleSameSupportTwoChargeFallbackSplitterReversed.blocks, ?split, ?gf2⟩
    · have hres :
          (splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
            (List.reverse (TseitinCycleCNFFormula 2 (by decide)))).residualCNF = [] := by
          simpa [twoCycleSameSupportTwoChargeFallbackSplitterReversed,
            CanonicalFingerprintGF2Decomposition.hasEmptyResidual] using
            twoCycleSameSupportTwoChargeFallbackSplitterReversed_hasEmptyResidual
      change
        splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
            (List.reverse (TseitinCycleCNFFormula 2 (by decide))) =
          { blocks :=
              (splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
                (List.reverse (TseitinCycleCNFFormula 2 (by decide)))).blocks,
            residualCNF := [] }
      cases h :
          splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback
            (List.reverse (TseitinCycleCNFFormula 2 (by decide))) with
      | mk blocks residualCNF =>
          simp [h] at hres ⊢
          exact hres
    · have hcore :
          canonicalFingerprintRecognizedBlocksGF2
              twoCycleSameSupportTwoChargeFallbackSplitterReversed.blocks =
            TseitinParityFormulaFromEncoding
              (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge := by
        simpa [CanonicalFingerprintGF2Decomposition.coreGF2] using
          twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreGF2_eq
      exact hcore ▸ List.Perm.refl _

/--
The enhanced fallback splitter satisfies the combined semantic/enhanced
executable package for every nonempty clause permutation of the direct
two-cycle boundary.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_of_perm
    {target : CNFModel.CNF
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 2 (by decide))).m}
    (hperm : List.Perm target (TseitinCycleCNFFormula 2 (by decide)))
    (hnonempty : target ≠ []) :
    EnhancedSemanticExtractorCompleteOn
      target
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge) := by
  let vars :=
    parityCandidateCanonicalSupportFromBlock
      (TseitinCycleCNFFormula 2 (by decide))
  have hgroups :
      groupClausesByCanonicalSupport target =
        [(GroupFrame.canonicalSupportKeyForVars vars, target)] := by
    simpa [vars] using
      groupClausesByCanonicalSupport_eq_single_of_perm_twoCycle
        hperm hnonempty
  have hinfer :
      inferCanonicalParityBlock target = none :=
    inferCanonicalParityBlock_eq_none_of_perm_twoCycle
      hperm hnonempty
  have hrec :
      recoverTwoChargeSameSupportGroupPerm? target =
        some twoCycleSameSupportFallbackDecomposition :=
    recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_twoCycle
      hperm hnonempty
  have hmain :
      EnhancedSemanticExtractorCompleteOn
        target
        twoCycleSameSupportFallbackDecomposition.coreGF2 :=
    enhancedSemanticExtractorCompleteOn_of_singleGroupTwoChargeFallback
      (f := target)
      (key := GroupFrame.canonicalSupportKeyForVars vars)
      (d := twoCycleSameSupportFallbackDecomposition)
      hgroups hinfer hrec
  have hcore :
      twoCycleSameSupportFallbackDecomposition.coreGF2 =
        TseitinParityFormulaFromEncoding
          (TseitinModel.encoding_cycle_derived 2 (by decide)) cycleRootCharge :=
    twoCycleSameSupportFallbackDecomposition_coreGF2_eq
  simpa [hcore] using hmain

/--
Every derived cycle with `1 < n` satisfies the combined semantic/enhanced
extraction claim.  The nondegenerate range uses the ordinary recognized-group
lane inside the enhanced splitter; the `n = 2` boundary uses the certified
two-charge same-support fallback.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula
    (n : Nat) (hn : 1 < n) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  by_cases hn2 : 2 < n
  · exact
      enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate
        n hn hn2
  · have hle : n <= 2 := Nat.le_of_not_gt hn2
    have hge : 2 <= n := Nat.succ_le_of_lt hn
    have htwo : n = 2 := Nat.le_antisymm hle hge
    subst n
    have hhn : hn = (by decide : 1 < 2) := Subsingleton.elim _ _
    cases hhn
    exact enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle

/--
Recognized canonical support groups yield a declarative `ParityEncoded.Class`
witness when their emitted blocks carry syntactic recognition signals and
append-disjointness.
-/
theorem class_of_groupRecognition_syntacticSignals
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  have hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] } := by
    unfold splitArityFourParityCanonicalSupportGroups
    rw [hgroups]
    exact
      ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
        hrec
  exact
    class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals
      hsplit hsyntactic hdisjoint

/--
The same group-recognition-to-class bridge, with syntactic recognition signals
discharged by successful executable `toSyntactic?` checks on every emitted
canonical block.
-/
theorem class_of_groupRecognition_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    class_of_groupRecognition_syntacticSignals
      hgroups hrec
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
      hdisjoint

/--
Recognized canonical support groups yield a declarative `ParityEncoded.Class`
witness through semantic append/gluing, with no support-disjointness premise on
the emitted blocks.
-/
theorem class_of_groupRecognition_syntacticSignals_append
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  have hblocksClass :
      ParityEncoded.Class m
        (canonicalFingerprintRecognizedBlocksCNF blocks)
        (canonicalFingerprintRecognizedBlocksGF2 blocks) :=
    class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append
      hsyntactic
  have hcover :
      List.Perm (canonicalFingerprintRecognizedBlocksCNF blocks) f :=
    canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized
      hgroups hrec
  exact ParityEncoded.Class.cnf_perm hcover hblocksClass

/--
The relaxed group-recognition-to-class bridge with syntactic recognition
signals discharged by successful executable `toSyntactic?` checks.
-/
theorem class_of_groupRecognition_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks) :
    ParityEncoded.Class m f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    class_of_groupRecognition_syntacticSignals_append
      hgroups hrec
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)

/--
A residual-free executable split yields the combined semantic/executable claim
when the emitted blocks carry syntactic recognition signals and
append-disjointness.
-/
theorem semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  apply ExtractorCompleteness.semanticExtractorCompleteOn_of_class
  case hclass =>
    exact
      class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals
        hsplit hsyntactic hdisjoint
  case hextract =>
    refine Exists.intro blocks ?_
    exact And.intro hsplit (List.Perm.refl _)

/--
The same residual-free split-to-combined bridge, with syntactic recognition
signals discharged by successful executable `toSyntactic?` checks on every
emitted canonical block.
-/
theorem semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals
      hsplit
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
      hdisjoint

/--
A residual-free executable split yields the combined semantic/executable claim
through semantic append/gluing, without requiring emitted blocks to be
support-disjoint.
-/
theorem semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  apply ExtractorCompleteness.semanticExtractorCompleteOn_of_class
  case hclass =>
    exact
      class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append
        hsplit hsyntactic
  case hextract =>
    refine Exists.intro blocks ?_
    exact And.intro hsplit (List.Perm.refl _)

/--
The relaxed residual-free split-to-combined bridge with syntactic recognition
signals discharged by successful executable `toSyntactic?` checks.
-/
theorem semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := blocks, residualCNF := [] })
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append
      hsplit
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)

/--
Recognized canonical support groups yield the combined semantic/executable
claim when their emitted blocks carry syntactic recognition signals and
append-disjointness.
-/
theorem semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  apply
    semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals
  case hsplit =>
    unfold splitArityFourParityCanonicalSupportGroups
    rw [hgroups]
    exact
      ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
        hrec
  case hsyntactic =>
    exact hsyntactic
  case hdisjoint =>
    exact hdisjoint

/--
The same group-recognition-to-combined bridge, with syntactic recognition
signals discharged by successful executable `toSyntactic?` checks on every
emitted canonical block.
-/
theorem semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks)
    (hdisjoint : CanonicalBlocksAppendDisjoint blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals
      hgroups hrec
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)
      hdisjoint

/--
Recognized canonical support groups yield the combined semantic/executable
claim through semantic append/gluing, with no support-disjointness premise on
the emitted blocks.
-/
theorem semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  apply ExtractorCompleteness.semanticExtractorCompleteOn_of_class
  case hclass =>
    exact
      class_of_groupRecognition_syntacticSignals_append
        hgroups hrec hsyntactic
  case hextract =>
    exact
      ExtractorCompleteness.extractorCompleteOn_of_groupRecognition
        hgroups hrec (List.Perm.refl _)

/--
The relaxed group-recognition-to-combined bridge with syntactic recognition
signals discharged by successful executable `toSyntactic?` checks.
-/
theorem semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append
      hgroups hrec
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)

/--
Recognized canonical support groups yield the combined
semantic/enhanced-executable claim through semantic append/gluing.  This is the
enhanced fallback analogue of
`semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append`.
-/
theorem enhancedSemanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksSyntacticSignals blocks) :
    EnhancedSemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  apply enhancedSemanticExtractorCompleteOn_of_class
  case hclass =>
    exact
      class_of_groupRecognition_syntacticSignals_append
        hgroups hrec hsyntactic
  case hextract =>
    exact
      enhancedExtractorCompleteOn_of_groupRecognition
        hgroups hrec (List.Perm.refl _)

/--
The enhanced group-recognition-to-combined bridge, with syntactic recognition
signals discharged by successful executable `toSyntactic?` checks.
-/
theorem enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks) :
    EnhancedSemanticExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2 blocks) := by
  exact
    enhancedSemanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append
      hgroups hrec
      (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)

/--
Permutation-aware enhanced group-recognition bridge.  This is the version used
by generated-family completeness results, where the recognizer emits compact
GF(2) equations up to permutation of the caller's target formula.
-/
theorem enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_perm
    {m : Nat} {f : CNFModel.CNF m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {s : ParityEncoded.GF2Formula m}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : ExtractorCompleteness.GroupsRecognized groups blocks)
    (hsyntactic : CanonicalBlocksToSyntacticOk blocks)
    (hgf2 : List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s) :
    EnhancedSemanticExtractorCompleteOn f s :=
  enhancedSemanticExtractorCompleteOn_of_class
    (ParityEncoded.Class.gf2_perm hgf2
      (class_of_groupRecognition_syntacticSignals_append
        hgroups hrec
        (CanonicalBlocksSyntacticSignals.of_toSyntacticOk hsyntactic)))
    (enhancedExtractorCompleteOn_of_groupRecognition
      hgroups hrec hgf2)

/--
Proof-carrying recognition certificate for an arbitrary CNF.  Unlike the
generated-family interfaces below, this certificate does not say where `f`
came from; it records only that the executable support grouper produced
recognized canonical blocks, that every emitted block passed the stronger
syntactic upgrade, and that the emitted compact equations match the caller's
target up to permutation.
-/
structure CertifiedRecognizedCNF (m : Nat)
    (f : CNFModel.CNF m) (s : ParityEncoded.GF2Formula m) where
  groups : List (CanonicalSupportClauseGroup m)
  blocks : List (CanonicalFingerprintRecognizedParityBlock m)
  groups_eq : groupClausesByCanonicalSupport f = groups
  recognized : ExtractorCompleteness.GroupsRecognized groups blocks
  syntactic : CanonicalBlocksToSyntacticOk blocks
  gf2_perm : List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s

/--
An arbitrary CNF with a proof-carrying recognition certificate is in the
declarative parity-encoded class for the certified compact GF(2) target.
-/
theorem class_of_certifiedRecognizedCNF
    {m : Nat} {f : CNFModel.CNF m} {s : ParityEncoded.GF2Formula m}
    (hcert : CertifiedRecognizedCNF m f s) :
    ParityEncoded.Class m f s := by
  exact
    ParityEncoded.Class.gf2_perm hcert.gf2_perm
      (class_of_groupRecognition_toSyntacticOk_append
        (f := f)
        (groups := hcert.groups)
        (blocks := hcert.blocks)
        hcert.groups_eq
        hcert.recognized
        hcert.syntactic)

/--
The baseline canonical splitter is residual-free on any arbitrary CNF with a
proof-carrying recognition certificate.
-/
theorem extractorCompleteOn_of_certifiedRecognizedCNF
    {m : Nat} {f : CNFModel.CNF m} {s : ParityEncoded.GF2Formula m}
    (hcert : CertifiedRecognizedCNF m f s) :
    ExtractorCompleteness.ExtractorCompleteOn f s :=
  ExtractorCompleteness.extractorCompleteOn_of_groupRecognition
    (f := f)
    (s := s)
    (groups := hcert.groups)
    (blocks := hcert.blocks)
    hcert.groups_eq
    hcert.recognized
    hcert.gf2_perm

/--
Any arbitrary CNF with a proof-carrying recognition certificate satisfies the
baseline combined semantic/executable extraction surface.
-/
theorem semanticExtractorCompleteOn_of_certifiedRecognizedCNF
    {m : Nat} {f : CNFModel.CNF m} {s : ParityEncoded.GF2Formula m}
    (hcert : CertifiedRecognizedCNF m f s) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f s :=
  ExtractorCompleteness.semanticExtractorCompleteOn_of_class
    (class_of_certifiedRecognizedCNF hcert)
    (extractorCompleteOn_of_certifiedRecognizedCNF hcert)

/--
The baseline canonical splitter remains residual-free after arbitrary whole-CNF
permutation of a proof-carrying recognized CNF.
-/
theorem extractorCompleteOn_of_certifiedRecognizedCNF_perm
    {m : Nat} {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hperm : List.Perm source target)
    (hcert : CertifiedRecognizedCNF m source s) :
    ExtractorCompleteness.ExtractorCompleteOn target s :=
  GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm
    (source := source)
    (target := target)
    (sourceBlocks := hcert.blocks)
    hperm
    (by simpa [hcert.groups_eq] using hcert.recognized)
    hcert.gf2_perm

/--
Any arbitrary whole-CNF permutation of a proof-carrying recognized CNF satisfies
the combined semantic/executable baseline extraction surface.
-/
theorem semanticExtractorCompleteOn_of_certifiedRecognizedCNF_perm
    {m : Nat} {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hperm : List.Perm source target)
    (hcert : CertifiedRecognizedCNF m source s) :
    ExtractorCompleteness.SemanticExtractorCompleteOn target s :=
  GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm
    (source := source)
    (target := target)
    (sourceBlocks := hcert.blocks)
    hperm
    (ParityEncoded.Class.sound (class_of_certifiedRecognizedCNF hcert))
    (by simpa [hcert.groups_eq] using hcert.recognized)
    hcert.gf2_perm

/--
The enhanced fallback splitter also stays residual-free on a certified
recognized CNF; the recognized-group path is taken before any same-support
fallback branch is needed.
-/
theorem enhancedExtractorCompleteOn_of_certifiedRecognizedCNF
    {m : Nat} {f : CNFModel.CNF m} {s : ParityEncoded.GF2Formula m}
    (hcert : CertifiedRecognizedCNF m f s) :
    EnhancedExtractorCompleteOn f s :=
  enhancedExtractorCompleteOn_of_groupRecognition
    (f := f)
    (s := s)
    (groups := hcert.groups)
    (blocks := hcert.blocks)
    hcert.groups_eq
    hcert.recognized
    hcert.gf2_perm

/--
Any arbitrary CNF with a proof-carrying recognition certificate satisfies the
enhanced combined semantic/executable extraction surface.
-/
theorem enhancedSemanticExtractorCompleteOn_of_certifiedRecognizedCNF
    {m : Nat} {f : CNFModel.CNF m} {s : ParityEncoded.GF2Formula m}
    (hcert : CertifiedRecognizedCNF m f s) :
    EnhancedSemanticExtractorCompleteOn f s :=
  enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_perm
    (f := f)
    (groups := hcert.groups)
    (blocks := hcert.blocks)
    (s := s)
    hcert.groups_eq
    hcert.recognized
    hcert.syntactic
    hcert.gf2_perm

/--
Single-block recognition certificate for an arbitrary clause-permuted parity
component.  This is a smaller witness than `CertifiedRecognizedCNF`: callers
provide the one-support-component grouping fact, the executable recognizer
result for that component, and the literal-level permutation certificate
showing that the block matches its inferred parity spec.
-/
structure ClausePermutedRecognizedBlock (m : Nat) where
  key : CanonicalClauseSupportKey
  block : CanonicalFingerprintRecognizedParityBlock m
  groups_eq :
    groupClausesByCanonicalSupport block.blockCNF = [(key, block.blockCNF)]
  inferred : inferCanonicalParityBlock block.blockCNF = some block
  block_perm : List.Perm block.blockCNF block.spec.expandedCNF

/--
Singleton executable recognition plus a successful syntactic upgrade yields the
smaller clause-permuted recognized-block certificate.
-/
def clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {key : CanonicalClauseSupportKey}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hgroups : groupClausesByCanonicalSupport f = [(key, f)])
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    ClausePermutedRecognizedBlock m := by
  have hblockCNF : block.blockCNF = f :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  refine
    { key := key
      block := block
      groups_eq := ?_
      inferred := ?_
      block_perm :=
        canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk block
          hsyntactic }
  · rw [hblockCNF]
    exact hgroups
  · rw [hblockCNF]
    exact hinfer

/--
Literal-level permutation evidence discharges the executable syntactic upgrade
for a clause-permuted recognized block.
-/
theorem ClausePermutedRecognizedBlock.toSyntacticOk
    {m : Nat} (hblock : ClausePermutedRecognizedBlock m) :
    hblock.block.toSyntactic?.isSome = true :=
  canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal
    hblock.block
    (by
      unfold parityBlockRecognitionSignal
      exact decide_eq_true hblock.block_perm)

/--
A single clause-permuted recognized block induces the general proof-carrying
recognized-CNF certificate for its singleton compact GF(2) equation.
-/
def certifiedRecognizedCNF_of_clausePermutedRecognizedBlock
    {m : Nat} (hblock : ClausePermutedRecognizedBlock m) :
    CertifiedRecognizedCNF m hblock.block.blockCNF [hblock.block.compactGF2] :=
  { groups := [(hblock.key, hblock.block.blockCNF)]
    blocks := [hblock.block]
    groups_eq := hblock.groups_eq
    recognized := And.intro hblock.inferred True.intro
    syntactic :=
      CanonicalBlocksToSyntacticOk.singleton hblock.block
        (ClausePermutedRecognizedBlock.toSyntacticOk hblock)
    gf2_perm := List.Perm.refl _ }

/--
Single clause-permuted recognized blocks instantiate the declarative
parity-encoded class without separately supplying a `toSyntactic?` certificate.
-/
theorem class_of_clausePermutedRecognizedBlock
    {m : Nat} (hblock : ClausePermutedRecognizedBlock m) :
    ParityEncoded.Class m hblock.block.blockCNF [hblock.block.compactGF2] :=
  class_of_certifiedRecognizedCNF
    (certifiedRecognizedCNF_of_clausePermutedRecognizedBlock hblock)

/--
Single clause-permuted recognized blocks are residual-free for the baseline
executable extractor.
-/
theorem extractorCompleteOn_of_clausePermutedRecognizedBlock
    {m : Nat} (hblock : ClausePermutedRecognizedBlock m) :
    ExtractorCompleteness.ExtractorCompleteOn
      hblock.block.blockCNF [hblock.block.compactGF2] :=
  extractorCompleteOn_of_certifiedRecognizedCNF
    (certifiedRecognizedCNF_of_clausePermutedRecognizedBlock hblock)

/--
Single clause-permuted recognized blocks satisfy the baseline combined
semantic/executable extraction surface.
-/
theorem semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock
    {m : Nat} (hblock : ClausePermutedRecognizedBlock m) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      hblock.block.blockCNF [hblock.block.compactGF2] :=
  semanticExtractorCompleteOn_of_certifiedRecognizedCNF
    (certifiedRecognizedCNF_of_clausePermutedRecognizedBlock hblock)

/--
Single clause-permuted recognized blocks are residual-free for the enhanced
two-charge fallback extractor.
-/
theorem enhancedExtractorCompleteOn_of_clausePermutedRecognizedBlock
    {m : Nat} (hblock : ClausePermutedRecognizedBlock m) :
    EnhancedExtractorCompleteOn
      hblock.block.blockCNF [hblock.block.compactGF2] :=
  enhancedExtractorCompleteOn_of_certifiedRecognizedCNF
    (certifiedRecognizedCNF_of_clausePermutedRecognizedBlock hblock)

/--
Single clause-permuted recognized blocks satisfy the enhanced combined
semantic/executable extraction surface.
-/
theorem enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock
    {m : Nat} (hblock : ClausePermutedRecognizedBlock m) :
    EnhancedSemanticExtractorCompleteOn
      hblock.block.blockCNF [hblock.block.compactGF2] :=
  enhancedSemanticExtractorCompleteOn_of_certifiedRecognizedCNF
    (certifiedRecognizedCNF_of_clausePermutedRecognizedBlock hblock)

/--
Any nonempty clause permutation of a generated parity expansion supplies the
singleton grouping fact needed by the smaller recognized-block certificate.
The executable recognizer result and `toSyntactic?` upgrade remain explicit
premises.
-/
def clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    ClausePermutedRecognizedBlock m := by
  have hblockCNF : block.blockCNF = f :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  refine
    { key := GroupFrame.canonicalSupportKeyForVars vars
      block := block
      groups_eq := ?_
      inferred := ?_
      block_perm :=
        canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk block
          hsyntactic }
  · rw [hblockCNF]
    exact
      GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex
        hperm hf
  · rw [hblockCNF]
    exact hinfer

/--
Clause permutations of generated parity expansions instantiate the declarative
class once the executable recognizer returns a syntactically upgradable block.
-/
theorem class_of_perm_clausesForVertex_toSyntacticOk
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (_hperm : List.Perm f (clausesForVertex vars charge))
    (_hf : f = c :: tail)
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    ParityEncoded.Class m f [block.compactGF2] := by
  have hblockCNF : block.blockCNF = f :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  have hclass :=
    class_of_canonicalFingerprintRecognizedBlock_perm block
      (canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk block
        hsyntactic)
  simpa [hblockCNF] using hclass

/--
Clause permutations of generated parity expansions are residual-free for the
baseline executable extractor once the executable recognizer returns a
syntactically upgradable block.
-/
theorem extractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hinfer : inferCanonicalParityBlock f = some block)
    (_hsyntactic : block.toSyntactic?.isSome = true) :
    ExtractorCompleteness.ExtractorCompleteOn f [block.compactGF2] := by
  apply ExtractorCompleteness.extractorCompleteOn_of_singleRecognizedGroup
    (key := GroupFrame.canonicalSupportKeyForVars vars)
    (block := block)
  · exact
      GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex
        hperm hf
  · exact hinfer
  · exact List.Perm.refl _

/--
Clause permutations of generated parity expansions satisfy the combined
semantic/baseline-executable surface once the executable recognizer returns a
syntactically upgradable block.
-/
theorem semanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f [block.compactGF2] := by
  exact
    ExtractorCompleteness.semanticExtractorCompleteOn_of_class
      (class_of_perm_clausesForVertex_toSyntacticOk
        hperm hf hinfer hsyntactic)
      (extractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk
        hperm hf hinfer hsyntactic)

/--
Clause permutations of generated parity expansions are residual-free for the
enhanced two-charge fallback extractor once the executable recognizer returns a
syntactically upgradable block.
-/
theorem enhancedExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hinfer : inferCanonicalParityBlock f = some block)
    (_hsyntactic : block.toSyntactic?.isSome = true) :
    EnhancedExtractorCompleteOn f [block.compactGF2] := by
  apply enhancedExtractorCompleteOn_of_groupRecognition
    (groups := [(GroupFrame.canonicalSupportKeyForVars vars, f)])
    (blocks := [block])
  · exact
      GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex
        hperm hf
  · exact And.intro hinfer True.intro
  · exact List.Perm.refl _

/--
Clause permutations of generated parity expansions satisfy the combined
semantic/enhanced-executable surface once the executable recognizer returns a
syntactically upgradable block.
-/
theorem enhancedSemanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    EnhancedSemanticExtractorCompleteOn f [block.compactGF2] := by
  exact
    enhancedSemanticExtractorCompleteOn_of_class
      (class_of_perm_clausesForVertex_toSyntacticOk
        hperm hf hinfer hsyntactic)
      (enhancedExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk
        hperm hf hinfer hsyntactic)

/--
False-charge clause permutations of generated parity expansions produce the
single-block certificate once the canonical fingerprint signal is supplied.
The public recognizer's `false`-first order supplies the executable inference.
-/
theorem clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = true) :
    exists hblock : ClausePermutedRecognizedBlock m,
      hblock.block.blockCNF = f /\
        hblock.block.compactGF2 = parityClauseForVertex vars false := by
  rcases
    inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal_of_signal
      hperm hf hnormal hsignal with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  have hblockCNF : block.blockCNF = f :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  let hblock : ClausePermutedRecognizedBlock m :=
    clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk
      hperm hf hinfer hsyntactic
  refine ⟨hblock, ?_, ?_⟩
  · simpa [hblock] using hblockCNF
  · simpa [hblock] using hcompact

/-- False-charge permuted generated atoms instantiate the declarative class. -/
theorem class_of_perm_clausesForVertex_false_normal_of_signal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = true) :
    ParityEncoded.Class m f [parityClauseForVertex vars false] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal
      hperm hf hnormal hsignal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hclass := class_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hclass

/-- False-charge permuted generated atoms satisfy the baseline combined surface. -/
theorem semanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = true) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      f [parityClauseForVertex vars false] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal
      hperm hf hnormal hsignal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem := semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/-- False-charge permuted generated atoms satisfy the enhanced combined surface. -/
theorem enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := false } :
          ParityBlockSyntacticSpec m) = true) :
    EnhancedSemanticExtractorCompleteOn
      f [parityClauseForVertex vars false] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal
      hperm hf hnormal hsignal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem :=
    enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/--
True-charge clause permutations of generated parity expansions produce the
single-block certificate once the positive canonical fingerprint signal is
supplied and the public recognizer's false-first attempt is known to miss.
-/
theorem clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal_of_signal_of_falseMiss
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := true } :
          ParityBlockSyntacticSpec m) = true)
    (hmiss : inferCanonicalParityBlockWithCharge f false = none) :
    exists hblock : ClausePermutedRecognizedBlock m,
      hblock.block.blockCNF = f /\
        hblock.block.compactGF2 = parityClauseForVertex vars true := by
  rcases
    inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal_of_signal_of_falseMiss
      hperm hf hnormal hsignal hmiss with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  have hblockCNF : block.blockCNF = f :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  let hblock : ClausePermutedRecognizedBlock m :=
    clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk
      hperm hf hinfer hsyntactic
  refine ⟨hblock, ?_, ?_⟩
  · simpa [hblock] using hblockCNF
  · simpa [hblock] using hcompact

/-- True-charge permuted generated atoms instantiate the declarative class. -/
theorem class_of_perm_clausesForVertex_true_normal_of_signal_of_falseMiss
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := true } :
          ParityBlockSyntacticSpec m) = true)
    (hmiss : inferCanonicalParityBlockWithCharge f false = none) :
    ParityEncoded.Class m f [parityClauseForVertex vars true] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal_of_signal_of_falseMiss
      hperm hf hnormal hsignal hmiss with
    ⟨hblock, hblockCNF, hcompact⟩
  have hclass := class_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hclass

/-- True-charge permuted generated atoms satisfy the baseline combined surface. -/
theorem semanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := true } :
          ParityBlockSyntacticSpec m) = true)
    (hmiss : inferCanonicalParityBlockWithCharge f false = none) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      f [parityClauseForVertex vars true] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal_of_signal_of_falseMiss
      hperm hf hnormal hsignal hmiss with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem := semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/-- True-charge permuted generated atoms satisfy the enhanced combined surface. -/
theorem enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hsignal :
      canonicalParityBlockRecognitionSignal f
        ({ vars := vars, charge := true } :
          ParityBlockSyntacticSpec m) = true)
    (hmiss : inferCanonicalParityBlockWithCharge f false = none) :
    EnhancedSemanticExtractorCompleteOn
      f [parityClauseForVertex vars true] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal_of_signal_of_falseMiss
      hperm hf hnormal hsignal hmiss with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem :=
    enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/--
False-charge clause permutations of generated parity expansions produce the
single-block certificate with no caller-supplied fingerprint premise.  The
canonical signal is discharged by generic fingerprint permutation invariance.
-/
theorem clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists hblock : ClausePermutedRecognizedBlock m,
      hblock.block.blockCNF = f /\
        hblock.block.compactGF2 = parityClauseForVertex vars false := by
  rcases
    inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal
      hperm hf hnormal with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  have hblockCNF : block.blockCNF = f :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  let hblock : ClausePermutedRecognizedBlock m :=
    clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk
      hperm hf hinfer hsyntactic
  refine ⟨hblock, ?_, ?_⟩
  · simpa [hblock] using hblockCNF
  · simpa [hblock] using hcompact

/-- False-charge permuted generated atoms instantiate the declarative class. -/
theorem class_of_perm_clausesForVertex_false_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ParityEncoded.Class m f [parityClauseForVertex vars false] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal
      hperm hf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hclass := class_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hclass

/-- False-charge permuted generated atoms satisfy the baseline combined surface. -/
theorem semanticExtractorCompleteOn_perm_clausesForVertex_false_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      f [parityClauseForVertex vars false] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal
      hperm hf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem := semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/-- False-charge permuted generated atoms satisfy the enhanced combined surface. -/
theorem enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars false))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    EnhancedSemanticExtractorCompleteOn
      f [parityClauseForVertex vars false] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal
      hperm hf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem :=
    enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/--
True-charge clause permutations of generated parity expansions produce the
single-block certificate with no caller-supplied fingerprint or false-miss
premise.  The false-first miss follows from transported true/false
fingerprint separation.
-/
theorem clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists hblock : ClausePermutedRecognizedBlock m,
      hblock.block.blockCNF = f /\
        hblock.block.compactGF2 = parityClauseForVertex vars true := by
  rcases
    inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal
      hperm hf hnormal with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  have hblockCNF : block.blockCNF = f :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  let hblock : ClausePermutedRecognizedBlock m :=
    clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk
      hperm hf hinfer hsyntactic
  refine ⟨hblock, ?_, ?_⟩
  · simpa [hblock] using hblockCNF
  · simpa [hblock] using hcompact

/-- True-charge permuted generated atoms instantiate the declarative class. -/
theorem class_of_perm_clausesForVertex_true_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ParityEncoded.Class m f [parityClauseForVertex vars true] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal
      hperm hf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hclass := class_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hclass

/-- True-charge permuted generated atoms satisfy the baseline combined surface. -/
theorem semanticExtractorCompleteOn_perm_clausesForVertex_true_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      f [parityClauseForVertex vars true] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal
      hperm hf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem := semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/-- True-charge permuted generated atoms satisfy the enhanced combined surface. -/
theorem enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars true))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    EnhancedSemanticExtractorCompleteOn
      f [parityClauseForVertex vars true] := by
  rcases
    clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal
      hperm hf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem :=
    enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/--
Recognizer-complete CNF fragment generated from arbitrary clause-permuted
recognized blocks.  The append constructor carries the function-level frame
condition needed by the executable grouping pass; this is the first
induction-shaped completeness class that no longer depends on the generated
spec-list encoder.
-/
inductive ClausePermutedRecognizedClass (m : Nat) :
    CNFModel.CNF m -> ParityEncoded.GF2Formula m -> Prop
  | empty :
      ClausePermutedRecognizedClass m [] []
  | atom (hblock : ClausePermutedRecognizedBlock m) :
      ClausePermutedRecognizedClass m
        hblock.block.blockCNF [hblock.block.compactGF2]
  | append_keyDisjoint {f g : CNFModel.CNF m}
      {s t : ParityEncoded.GF2Formula m}
      (hf : ClausePermutedRecognizedClass m f s)
      (hg : ClausePermutedRecognizedClass m g t)
      (hkeyDisjoint : GroupFrame.CNFClauseKeysDisjoint f g) :
      ClausePermutedRecognizedClass m (f ++ g) (s ++ t)
  | cnf_perm {f g : CNFModel.CNF m}
      {s : ParityEncoded.GF2Formula m}
      (hperm : List.Perm f g)
      (hf : ClausePermutedRecognizedClass m f s) :
      ClausePermutedRecognizedClass m g s
  | gf2_perm {f : CNFModel.CNF m}
      {s t : ParityEncoded.GF2Formula m}
      (hperm : List.Perm s t)
      (hf : ClausePermutedRecognizedClass m f s) :
      ClausePermutedRecognizedClass m f t

/--
Recognizer-complete fragments are closed under arbitrary whole-CNF clause
permutation.  This is a named wrapper around the class constructor so external
theorem inventories can cite the closure property directly.
-/
theorem clausePermutedRecognizedClass_of_cnf_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hperm : List.Perm source target)
    (hclass : ClausePermutedRecognizedClass m source s) :
    ClausePermutedRecognizedClass m target s :=
  ClausePermutedRecognizedClass.cnf_perm hperm hclass

/--
Recognizer-complete fragments compose after each side is independently
clause-permuted, provided the original fragments were clause-key disjoint.
This is the class-level counterpart of the permuted-fragment frame lemmas in
`GroupFrame`.
-/
theorem clausePermutedRecognizedClass_append_keyDisjoint_perm
    {m : Nat}
    {f f' g g' : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hfperm : List.Perm f' f)
    (hgperm : List.Perm g' g)
    (hf : ClausePermutedRecognizedClass m f' s)
    (hg : ClausePermutedRecognizedClass m g' t)
    (hkeyDisjoint : GroupFrame.CNFClauseKeysDisjoint f g) :
    ClausePermutedRecognizedClass m (f' ++ g') (s ++ t) :=
  ClausePermutedRecognizedClass.append_keyDisjoint hf hg
    (GroupFrame.cnfClauseKeysDisjoint_of_perm
      hfperm hgperm hkeyDisjoint)

/--
Recognizer-complete fragments also compose when the two key-disjoint fragments
are appended in swapped CNF order; the GF(2) target is transported back to the
original fragment order by `gf2_perm`.
-/
theorem clausePermutedRecognizedClass_append_comm_keyDisjoint
    {m : Nat}
    {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hf : ClausePermutedRecognizedClass m f s)
    (hg : ClausePermutedRecognizedClass m g t)
    (hkeyDisjoint : GroupFrame.CNFClauseKeysDisjoint f g) :
    ClausePermutedRecognizedClass m (g ++ f) (s ++ t) := by
  have hswap :
      ClausePermutedRecognizedClass m (g ++ f) (t ++ s) :=
    ClausePermutedRecognizedClass.append_keyDisjoint hg hf
      (GroupFrame.cnfClauseKeysDisjoint_symm hkeyDisjoint)
  exact
    ClausePermutedRecognizedClass.gf2_perm
      (List.perm_append_comm : List.Perm (t ++ s) (s ++ t))
      hswap

/--
The clause-permuted recognizer-complete fragment forgets to the declarative
parity-encoded class.
-/
theorem class_of_clausePermutedRecognizedClass
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hclass : ClausePermutedRecognizedClass m f s) :
    ParityEncoded.Class m f s := by
  induction hclass with
  | empty =>
      exact ParityEncoded.Class.empty
  | atom hblock =>
      exact class_of_clausePermutedRecognizedBlock hblock
  | append_keyDisjoint _hf _hg _hkeyDisjoint ihf ihg =>
      exact ParityEncoded.Class.append ihf ihg
  | cnf_perm hperm _hf ih =>
      exact ParityEncoded.Class.cnf_perm hperm ih
  | gf2_perm hperm _hf ih =>
      exact ParityEncoded.Class.gf2_perm hperm ih

/--
Empty CNFs are residual-free for the baseline executable extractor.
-/
theorem extractorCompleteOn_empty
    {m : Nat} :
    ExtractorCompleteness.ExtractorCompleteOn
      ([] : CNFModel.CNF m) [] := by
  apply ExtractorCompleteness.extractorCompleteOn_of_groupRecognition
    (f := ([] : CNFModel.CNF m))
    (groups := [])
    (blocks := [])
  · rfl
  · exact True.intro
  · simp [canonicalFingerprintRecognizedBlocksGF2]

/--
Every clause-permuted recognizer-complete fragment carries recognized
executable support groups whose compact GF(2) output matches the class target
up to `List.Perm`.
-/
theorem groupsRecognized_exists_of_clausePermutedRecognizedClass
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hclass : ClausePermutedRecognizedClass m f s) :
    exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) blocks /\
        List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s := by
  induction hclass with
  | empty =>
      exact Exists.intro [] (And.intro True.intro (List.Perm.refl []))
  | atom hblock =>
      refine Exists.intro [hblock.block] ?_
      constructor
      · rw [hblock.groups_eq]
        exact And.intro hblock.inferred True.intro
      · exact List.Perm.refl _
  | append_keyDisjoint _hf _hg hkeyDisjoint ihf ihg =>
      rcases ihf with ⟨leftBlocks, hleftRecognized, hleftGF2⟩
      rcases ihg with ⟨rightBlocks, hrightRecognized, hrightGF2⟩
      refine Exists.intro (leftBlocks ++ rightBlocks) ?_
      constructor
      · rw [GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
          _ _ hkeyDisjoint]
        exact
          ExtractorCompleteness.GroupsRecognized.append
            hleftRecognized hrightRecognized
      · rw [canonicalFingerprintRecognizedBlocksGF2_append]
        exact hleftGF2.append hrightGF2
  | cnf_perm hperm _hf ih =>
      rcases ih with ⟨sourceBlocks, hsourceRecognized, hsourceGF2⟩
      rcases
        GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm
          hperm hsourceRecognized with
        ⟨targetBlocks, htargetRecognized, htargetGF2⟩
      exact
        Exists.intro targetBlocks
          (And.intro htargetRecognized
            (List.Perm.trans htargetGF2 hsourceGF2))
  | gf2_perm hperm _hf ih =>
      rcases ih with ⟨blocks, hrecognized, hgf2⟩
      exact
        Exists.intro blocks
          (And.intro hrecognized (List.Perm.trans hgf2 hperm))

/--
The clause-permuted recognizer-complete fragment is residual-free for the
baseline executable extractor.
-/
theorem extractorCompleteOn_of_clausePermutedRecognizedClass
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hclass : ClausePermutedRecognizedClass m f s) :
    ExtractorCompleteness.ExtractorCompleteOn f s := by
  induction hclass with
  | empty =>
      exact extractorCompleteOn_empty
  | atom hblock =>
      exact extractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  | append_keyDisjoint _hf _hg hkeyDisjoint ihf ihg =>
      exact
        GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint
          hkeyDisjoint ihf ihg
  | cnf_perm hperm _hf _ih =>
      rcases
        groupsRecognized_exists_of_clausePermutedRecognizedClass
          (ClausePermutedRecognizedClass.cnf_perm hperm _hf) with
        ⟨blocks, hrecognized, hgf2⟩
      exact
        ExtractorCompleteness.extractorCompleteOn_of_groupRecognition
          (f := _)
          (groups := groupClausesByCanonicalSupport _)
          (blocks := blocks)
          rfl hrecognized hgf2
  | gf2_perm hperm _hf ih =>
      rcases ih with ⟨blocks, hsplit, hgf2⟩
      exact ⟨blocks, hsplit, List.Perm.trans hgf2 hperm⟩

/--
The clause-permuted recognizer-complete fragment satisfies the combined
semantic/baseline-executable surface.
-/
theorem semanticExtractorCompleteOn_of_clausePermutedRecognizedClass
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hclass : ClausePermutedRecognizedClass m f s) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f s :=
  ExtractorCompleteness.semanticExtractorCompleteOn_of_class
    (class_of_clausePermutedRecognizedClass hclass)
    (extractorCompleteOn_of_clausePermutedRecognizedClass hclass)

/--
The baseline canonical splitter remains residual-free after arbitrary whole-CNF
permutation of a clause-permuted recognizer-complete fragment.
-/
theorem extractorCompleteOn_of_clausePermutedRecognizedClass_perm
    {m : Nat} {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hperm : List.Perm source target)
    (hclass : ClausePermutedRecognizedClass m source s) :
    ExtractorCompleteness.ExtractorCompleteOn target s := by
  rcases
    groupsRecognized_exists_of_clausePermutedRecognizedClass hclass with
    ⟨blocks, hrecognized, hgf2⟩
  exact
    GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm
      (source := source)
      (target := target)
      (sourceBlocks := blocks)
      hperm hrecognized hgf2

/--
Any arbitrary whole-CNF permutation of a clause-permuted recognizer-complete
fragment satisfies the combined semantic/executable baseline extraction
surface.
-/
theorem semanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm
    {m : Nat} {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hperm : List.Perm source target)
    (hclass : ClausePermutedRecognizedClass m source s) :
    ExtractorCompleteness.SemanticExtractorCompleteOn target s := by
  rcases
    groupsRecognized_exists_of_clausePermutedRecognizedClass hclass with
    ⟨blocks, hrecognized, hgf2⟩
  exact
    GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm
      (source := source)
      (target := target)
      (sourceBlocks := blocks)
      hperm
      (ParityEncoded.Class.sound
        (class_of_clausePermutedRecognizedClass hclass))
      hrecognized hgf2

/--
Empty CNFs are residual-free for the enhanced two-charge fallback extractor.
-/
theorem enhancedExtractorCompleteOn_empty
    {m : Nat} :
    EnhancedExtractorCompleteOn ([] : CNFModel.CNF m) [] := by
  apply enhancedExtractorCompleteOn_of_groupRecognition
    (f := ([] : CNFModel.CNF m))
    (groups := [])
    (blocks := [])
  · rfl
  · exact True.intro
  · simp [canonicalFingerprintRecognizedBlocksGF2]

/--
The clause-permuted recognizer-complete fragment is residual-free for the
enhanced two-charge fallback extractor.
-/
theorem enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hclass : ClausePermutedRecognizedClass m f s) :
    EnhancedExtractorCompleteOn f s := by
  induction hclass with
  | empty =>
      exact enhancedExtractorCompleteOn_empty
  | atom hblock =>
      exact enhancedExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  | append_keyDisjoint _hf _hg hkeyDisjoint ihf ihg =>
      exact enhancedExtractorCompleteOn_append_of_clauseKeysDisjoint
        hkeyDisjoint ihf ihg
  | cnf_perm hperm _hf _ih =>
      rcases
        groupsRecognized_exists_of_clausePermutedRecognizedClass
          (ClausePermutedRecognizedClass.cnf_perm hperm _hf) with
        ⟨blocks, hrecognized, hgf2⟩
      exact
        enhancedExtractorCompleteOn_of_groupRecognition
          (f := _)
          (groups := groupClausesByCanonicalSupport _)
          (blocks := blocks)
          rfl hrecognized hgf2
  | gf2_perm hperm _hf ih =>
      rcases ih with ⟨blocks, hsplit, hgf2⟩
      exact ⟨blocks, hsplit, List.Perm.trans hgf2 hperm⟩

/--
The clause-permuted recognizer-complete fragment satisfies the combined
semantic/enhanced-executable surface.
-/
theorem enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hclass : ClausePermutedRecognizedClass m f s) :
    EnhancedSemanticExtractorCompleteOn f s :=
  enhancedSemanticExtractorCompleteOn_of_class
    (class_of_clausePermutedRecognizedClass hclass)
    (enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass hclass)

/--
The enhanced two-charge fallback splitter remains residual-free after arbitrary
whole-CNF permutation of a clause-permuted recognizer-complete fragment.
-/
theorem enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass_perm
    {m : Nat} {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hperm : List.Perm source target)
    (hclass : ClausePermutedRecognizedClass m source s) :
    EnhancedExtractorCompleteOn target s :=
  enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass
    (ClausePermutedRecognizedClass.cnf_perm hperm hclass)

/--
Any arbitrary whole-CNF permutation of a clause-permuted recognizer-complete
fragment satisfies the combined semantic/enhanced-executable extraction
surface.
-/
theorem enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm
    {m : Nat} {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hperm : List.Perm source target)
    (hclass : ClausePermutedRecognizedClass m source s) :
    EnhancedSemanticExtractorCompleteOn target s :=
  enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass
    (ClausePermutedRecognizedClass.cnf_perm hperm hclass)

/--
Nonempty clause permutations of generated parity atoms in canonical support
order instantiate the recognizer-complete class directly.  This is the atom
case needed by future class-level completeness theorems; it uses the canonical
fingerprint permutation-invariance result to avoid caller-supplied recognizer
signals.
-/
theorem clausePermutedRecognizedClass_of_perm_clausesForVertex_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ClausePermutedRecognizedClass m
      f [parityClauseForVertex vars charge] := by
  cases charge
  · rcases
      clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal
        hperm hf hnormal with
      ⟨hblock, hblockCNF, hcompact⟩
    have hclass := ClausePermutedRecognizedClass.atom hblock
    simpa [hblockCNF, hcompact] using hclass
  · rcases
      clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal
        hperm hf hnormal with
      ⟨hblock, hblockCNF, hcompact⟩
    have hclass := ClausePermutedRecognizedClass.atom hblock
    simpa [hblockCNF, hcompact] using hclass

/--
Generated parity atoms in canonical support order produce the smaller
clause-permuted recognized-block certificate.
-/
theorem clausePermutedRecognizedBlock_exists_clausesForVertex_normal
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    exists hblock : ClausePermutedRecognizedBlock m,
      hblock.block.blockCNF = clausesForVertex vars charge /\
        hblock.block.compactGF2 = parityClauseForVertex vars charge := by
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf hnormal with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  have hblockCNF : block.blockCNF = clausesForVertex vars charge :=
    ExtractorCompleteness.blockCNF_eq_of_inferCanonicalParityBlock hinfer
  let hblock : ClausePermutedRecognizedBlock m :=
    clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk
      (m := m)
      (f := clausesForVertex vars charge)
      (key := GroupFrame.canonicalSupportKeyForVars vars)
      (block := block)
      (GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
        hcnf)
      hinfer
      hsyntactic
  refine ⟨hblock, ?_, ?_⟩
  · simpa [hblock] using hblockCNF
  · simpa [hblock] using hcompact

/--
Generated parity atoms instantiate the declarative class through the
clause-permuted recognized-block certificate.
-/
theorem class_of_clausesForVertex_normal_via_clausePermutedRecognizedBlock
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ParityEncoded.Class m
      (clausesForVertex vars charge)
      [parityClauseForVertex vars charge] := by
  rcases
    clausePermutedRecognizedBlock_exists_clausesForVertex_normal
      hcnf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hclass := class_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hclass

/--
Generated parity atoms satisfy the baseline combined semantic/executable
surface through the clause-permuted recognized-block certificate.
-/
theorem semanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (clausesForVertex vars charge)
      [parityClauseForVertex vars charge] := by
  rcases
    clausePermutedRecognizedBlock_exists_clausesForVertex_normal
      hcnf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem := semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/--
Generated parity atoms satisfy the enhanced combined semantic/executable
surface through the clause-permuted recognized-block certificate.
-/
theorem enhancedSemanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    EnhancedSemanticExtractorCompleteOn
      (clausesForVertex vars charge)
      [parityClauseForVertex vars charge] := by
  rcases
    clausePermutedRecognizedBlock_exists_clausesForVertex_normal
      hcnf hnormal with
    ⟨hblock, hblockCNF, hcompact⟩
  have hsem :=
    enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock hblock
  simpa [hblockCNF, hcompact] using hsem

/--
Generated key-disjoint families instantiate the more general
clause-permuted recognizer-complete fragment.
-/
theorem clausePermutedRecognizedClass_of_generatedKeyDisjointFamily
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedKeyDisjointFamily m f s) :
    ClausePermutedRecognizedClass m f s := by
  induction hfamily with
  | empty =>
      exact ClausePermutedRecognizedClass.empty
  | snoc _hprefix hkeyDisjoint hcnf hnormal ih =>
      rename_i _fPrefix _sPrefix vars charge _c _tail
      rcases
        clausePermutedRecognizedBlock_exists_clausesForVertex_normal
          hcnf hnormal with
        ⟨hblock, hblockCNF, hcompact⟩
      have hatom :
          ClausePermutedRecognizedClass m
            (clausesForVertex vars charge)
            [parityClauseForVertex vars charge] := by
        have hbase := ClausePermutedRecognizedClass.atom hblock
        simpa [hblockCNF, hcompact] using hbase
      exact
        ClausePermutedRecognizedClass.append_keyDisjoint
          ih hatom hkeyDisjoint

/--
Generated key-disjoint spec lists instantiate the clause-permuted
recognizer-complete fragment.
-/
theorem clausePermutedRecognizedClass_of_generatedKeyDisjointSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    ClausePermutedRecognizedClass m
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  clausePermutedRecognizedClass_of_generatedKeyDisjointFamily
    (generatedKeyDisjointFamily_of_specList hspecs)

/--
Generated spec lists with fresh canonical support keys instantiate the
clause-permuted recognizer-complete fragment.
-/
theorem clausePermutedRecognizedClass_of_generatedCanonicalKeyFreshSpecList
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    ClausePermutedRecognizedClass m
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  clausePermutedRecognizedClass_of_generatedKeyDisjointSpecList
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Generated key-disjoint families satisfy the enhanced semantic/executable claim
directly through their recognized support groups and executable syntactic
upgrade certificates.
-/
theorem enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointFamily_toSyntacticOk
    {m : Nat}
    {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    (hfamily : GeneratedKeyDisjointFamily m f s) :
    EnhancedSemanticExtractorCompleteOn f s := by
  rcases
    groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointFamily
      hfamily with
    ⟨blocks, hrec, hsyntactic, hgf2⟩
  exact
    enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_perm
      (f := f)
      (groups := groupClausesByCanonicalSupport f)
      (blocks := blocks)
      (s := s)
      rfl hrec hsyntactic hgf2

/--
Generated key-disjoint spec lists inherit the direct recognizer-certificate
route to the enhanced semantic/executable claim.
-/
theorem enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList_toSyntacticOk
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedKeyDisjointSpecList m specs) :
    EnhancedSemanticExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointFamily_toSyntacticOk
    (generatedKeyDisjointFamily_of_specList hspecs)

/--
Generated spec lists with fresh canonical support keys inherit the direct
recognizer-certificate route to the enhanced semantic/executable claim.
-/
theorem enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
    {m : Nat}
    {specs : List (GeneratedParitySpec m)}
    (hspecs : GeneratedCanonicalKeyFreshSpecList m specs) :
    EnhancedSemanticExtractorCompleteOn
      (generatedParitySpecsCNF specs)
      (generatedParitySpecsGF2 specs) :=
  enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList_toSyntacticOk
    (generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList hspecs)

/--
Concrete graph encodings whose generated incident specs are key-disjoint
inherit the direct recognizer-certificate route to the enhanced
semantic/executable claim.
-/
theorem enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList_toSyntacticOk
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  rw [(generatedParitySpecsCNF_fromEncoding enc charge).symm,
    (generatedParitySpecsGF2_fromEncoding enc charge).symm]
  exact enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList_toSyntacticOk
    hspecs

/--
Concrete graph encodings whose generated incident specs have fresh canonical
support keys inherit the direct recognizer-certificate route to the enhanced
semantic/executable claim.
-/
theorem enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph enc).m
        (generatedParitySpecsFromEncoding enc charge)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  rw [(generatedParitySpecsCNF_fromEncoding enc charge).symm,
    (generatedParitySpecsGF2_fromEncoding enc charge).symm]
  exact
    enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
      hspecs

/--
Concrete graph encodings with nonempty generated vertex blocks and fresh
canonical incident-support keys inherit the direct recognizer-certificate
route to the enhanced semantic/executable claim.
-/
theorem enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_toSyntacticOk
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hcnf :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v : Nat,
        v < G.n ->
          exists c : CNFModel.Clause G.m,
            exists tail : CNFModel.CNF G.m,
              clausesForVertex (incidentIndices G hme v) (charge v) = c :: tail) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh
      enc charge hfresh hcnf)

/--
Concrete graph encodings with positive vertex degree and fresh canonical
incident-support keys inherit the direct recognizer-certificate route to the
enhanced semantic/executable claim.
-/
theorem enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos_toSyntacticOk
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hfresh :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)))
    (hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat,
        v < G.n -> 0 < TseitinModel.degree G v) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) :=
  enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
    enc charge
    (generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos
      enc charge hfresh hdegree)

/--
The derived `circulant12` graph family inherits the direct
recognizer-certificate route once its canonical incident-support keys are
fresh. The positive-degree side condition is discharged by the graph-family
degree theorem.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh_toSyntacticOk
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool)
    (hfresh :
      let enc := TseitinModel.encoding_circulant12_derived n hn
      let G := TseitinModel.GraphEncodingData.toGraph enc
      let hme := TseitinModel.m_eq_edges_length_of_encoding enc
      forall v prior : Nat,
        v < G.n ->
          prior < v ->
            Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
              GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior))) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) := by
  let enc := TseitinModel.encoding_circulant12_derived n hn
  have hdegree :
      let G := TseitinModel.GraphEncodingData.toGraph enc
      forall v : Nat, v < G.n -> 0 < TseitinModel.degree G v := by
    dsimp [enc]
    intro v hv
    exact TseitinModel.circulant12_degree_pos n v hn hv
  exact
    enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos_toSyntacticOk
      enc charge hfresh hdegree

/--
The derived `circulant12` graph family satisfies the combined
semantic/enhanced extraction claim through the direct recognizer-certificate
route.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_toSyntacticOk
    (n : Nat) (hn : 2 < n) (charge : Nat -> Bool) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_circulant12_derived n hn) charge) :=
  enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh_toSyntacticOk
    n hn charge (circulant12IncidentSupportKeys_fresh n hn)

/--
Cycle-family enhanced semantic/executable completeness reduces to the
key-disjoint generated incident-spec side condition through the direct
recognizer-certificate route.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList_toSyntacticOk
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedKeyDisjointSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  dsimp [TseitinCycleCNFFormula, generatedParitySpecsForCycle]
  exact
    enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList_toSyntacticOk
      (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge hspecs

/--
Cycle-family enhanced semantic/executable completeness also reduces to the
canonical-key-fresh generated incident-spec side condition through the direct
recognizer-certificate route.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
    (n : Nat) (hn : 1 < n)
    (hspecs :
      GeneratedCanonicalKeyFreshSpecList
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)).m
        (generatedParitySpecsForCycle n hn)) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  dsimp [TseitinCycleCNFFormula, generatedParitySpecsForCycle]
  exact
    enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
      (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge hspecs

/--
Nondegenerate derived cycles satisfy the combined semantic/enhanced extraction
claim through the direct recognizer-certificate route.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate_toSyntacticOk
    (n : Nat) (hn : 1 < n) (hn2 : 2 < n) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) :=
  enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk
    n hn (generatedCanonicalKeyFreshSpecList_forCycle n hn hn2)

/--
Every derived cycle with `1 < n` satisfies the combined semantic/enhanced
extraction claim, using the direct recognizer-certificate route in the
nondegenerate range and the certified two-charge fallback at the two-cycle
boundary.
-/
theorem enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_toSyntacticOk
    (n : Nat) (hn : 1 < n) :
    EnhancedSemanticExtractorCompleteOn
      (TseitinCycleCNFFormula n hn)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge) := by
  by_cases hn2 : 2 < n
  · exact
      enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate_toSyntacticOk
        n hn hn2
  · have hle : n <= 2 := Nat.le_of_not_gt hn2
    have hge : 2 <= n := Nat.succ_le_of_lt hn
    have htwo : n = 2 := Nat.le_antisymm hle hge
    subst n
    have hhn : hn = (by decide : 1 < 2) := Subsingleton.elim _ _
    cases hhn
    exact enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle

/--
Single-support-group combined bridge for the executable canonical splitter.
Once a CNF groups as one support component, the canonical recognizer returns
one block, and the block passes `toSyntactic?`, the CNF satisfies the combined
semantic/executable extraction claim for that emitted GF(2) equation.
-/
theorem semanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {key : CanonicalClauseSupportKey}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hgroups : groupClausesByCanonicalSupport f = [(key, f)])
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    ExtractorCompleteness.SemanticExtractorCompleteOn f [block.compactGF2] := by
  have hsyntacticList :
      CanonicalBlocksToSyntacticOk [block] :=
    CanonicalBlocksToSyntacticOk.singleton block hsyntactic
  have hdisjoint :
      CanonicalBlocksAppendDisjoint [block] :=
    CanonicalBlocksAppendDisjoint.singleton block
  simpa [canonicalFingerprintRecognizedBlocksGF2] using
    semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk
      (f := f)
      (groups := [(key, f)])
      (blocks := [block])
      hgroups
      (And.intro hinfer True.intro)
      hsyntacticList
      hdisjoint

/--
Single-support-group combined bridge for the enhanced fallback splitter.  When
the ordinary one-block recognizer succeeds, the enhanced splitter takes the
same recognized path and satisfies the enhanced combined surface.
-/
theorem enhancedSemanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {key : CanonicalClauseSupportKey}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hgroups : groupClausesByCanonicalSupport f = [(key, f)])
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    EnhancedSemanticExtractorCompleteOn f [block.compactGF2] := by
  have hsyntacticList :
      CanonicalBlocksToSyntacticOk [block] :=
    CanonicalBlocksToSyntacticOk.singleton block hsyntactic
  simpa [canonicalFingerprintRecognizedBlocksGF2] using
    enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append
      (f := f)
      (groups := [(key, f)])
      (blocks := [block])
      hgroups
      (And.intro hinfer True.intro)
      hsyntacticList

/--
Single-support-group bridge for the executable canonical splitter.  Once a
CNF is known to group as one support component, the canonical recognizer returns
one block, and the block passes the executable syntactic upgrade, the CNF is a
declarative parity-encoded atom.
-/
theorem class_of_singleGroupRecognition_toSyntacticOk
    {m : Nat} {f : CNFModel.CNF m}
    {key : CanonicalClauseSupportKey}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hgroups : groupClausesByCanonicalSupport f = [(key, f)])
    (hinfer : inferCanonicalParityBlock f = some block)
    (hsyntactic : block.toSyntactic?.isSome = true) :
    ParityEncoded.Class m f [block.compactGF2] := by
  have hsplit :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := [block], residualCNF := [] } := by
    unfold splitArityFourParityCanonicalSupportGroups
    rw [hgroups]
    simp [splitCanonicalSupportClauseGroups, hinfer]
  have hsyntacticList :
      CanonicalBlocksToSyntacticOk [block] :=
    CanonicalBlocksToSyntacticOk.singleton block hsyntactic
  have hdisjoint :
      CanonicalBlocksAppendDisjoint [block] :=
    CanonicalBlocksAppendDisjoint.singleton block
  simpa [canonicalFingerprintRecognizedBlocksGF2] using
    class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk
      hsplit hsyntacticList hdisjoint

/--
Support-disjoint append fragment for the executable canonical splitter.  If
both sides group into recognized canonical blocks, all emitted blocks pass the
executable syntactic upgrade check, and each side is internally append-disjoint,
then the appended CNF has a declarative `ParityEncoded.Class` witness.
-/
theorem class_of_disjoint_appendGroupRecognition_toSyntacticOk
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) leftBlocks)
    (hright :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport g) rightBlocks)
    (hleftSyntactic : CanonicalBlocksToSyntacticOk leftBlocks)
    (hrightSyntactic : CanonicalBlocksToSyntacticOk rightBlocks)
    (hleftDisjoint : CanonicalBlocksAppendDisjoint leftBlocks)
    (hrightDisjoint : CanonicalBlocksAppendDisjoint rightBlocks) :
    ParityEncoded.Class m (f ++ g)
      (canonicalFingerprintRecognizedBlocksGF2
        (leftBlocks ++ rightBlocks)) := by
  have hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g :=
    GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
      f g hdisjoint hnonempty
  have hsplit :
      splitArityFourParityCanonicalSupportGroups (f ++ g) =
        { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } := by
    unfold splitArityFourParityCanonicalSupportGroups
    rw [hgroups]
    exact
      ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
        (ExtractorCompleteness.GroupsRecognized.append hleft hright)
  have hsyntactic :
      CanonicalBlocksToSyntacticOk (leftBlocks ++ rightBlocks) :=
    CanonicalBlocksToSyntacticOk.append hleftSyntactic hrightSyntactic
  have hleftCover :
      List.Perm
        (canonicalFingerprintRecognizedBlocksCNF leftBlocks)
        f :=
    canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized
      (f := f) rfl hleft
  have hrightCover :
      List.Perm
        (canonicalFingerprintRecognizedBlocksCNF rightBlocks)
        g :=
    canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized
      (f := g) rfl hright
  have hcovered :
      ParityEncoded.DisjointSupport
        (canonicalFingerprintRecognizedBlocksCNF leftBlocks)
        (canonicalFingerprintRecognizedBlocksCNF rightBlocks) :=
    disjointSupport_of_perm hdisjoint hleftCover hrightCover
  have happendDisjoint :
      CanonicalBlocksAppendDisjoint (leftBlocks ++ rightBlocks) :=
    CanonicalBlocksAppendDisjoint.append_of_disjointCovered
      hleftDisjoint hrightDisjoint hcovered
  exact
    class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk
      hsplit hsyntactic happendDisjoint

/--
Support-disjoint append fragment for the executable canonical splitter, using
semantic append/gluing for the emitted block list.  The source fragments still
need to frame the grouping pass, but the emitted blocks do not need internal
append-disjointness.
-/
theorem class_of_disjoint_appendGroupRecognition_toSyntacticOk_append
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) leftBlocks)
    (hright :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport g) rightBlocks)
    (hleftSyntactic : CanonicalBlocksToSyntacticOk leftBlocks)
    (hrightSyntactic : CanonicalBlocksToSyntacticOk rightBlocks) :
    ParityEncoded.Class m (f ++ g)
      (canonicalFingerprintRecognizedBlocksGF2
        (leftBlocks ++ rightBlocks)) := by
  have hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g :=
    GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
      f g hdisjoint hnonempty
  have hsyntactic :
      CanonicalBlocksToSyntacticOk (leftBlocks ++ rightBlocks) :=
    CanonicalBlocksToSyntacticOk.append hleftSyntactic hrightSyntactic
  exact
    class_of_groupRecognition_toSyntacticOk_append
      (f := f ++ g)
      (groups :=
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g)
      (blocks := leftBlocks ++ rightBlocks)
      hgroups
      (ExtractorCompleteness.GroupsRecognized.append hleft hright)
      hsyntactic

/--
Support-disjoint append fragment for the combined semantic/executable surface.
If both sides group into recognized canonical blocks, the right side has no
empty-support clauses, emitted blocks pass the executable syntactic upgrade
check, and each side is internally append-disjoint, then `F ++ G` satisfies the
combined extractor-completeness claim.
-/
theorem semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) leftBlocks)
    (hright :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport g) rightBlocks)
    (hleftSyntactic : CanonicalBlocksToSyntacticOk leftBlocks)
    (hrightSyntactic : CanonicalBlocksToSyntacticOk rightBlocks)
    (hleftDisjoint : CanonicalBlocksAppendDisjoint leftBlocks)
    (hrightDisjoint : CanonicalBlocksAppendDisjoint rightBlocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn (f ++ g)
      (canonicalFingerprintRecognizedBlocksGF2
        (leftBlocks ++ rightBlocks)) := by
  have hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g :=
    GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
      f g hdisjoint hnonempty
  have hsyntactic :
      CanonicalBlocksToSyntacticOk (leftBlocks ++ rightBlocks) :=
    CanonicalBlocksToSyntacticOk.append hleftSyntactic hrightSyntactic
  have hleftCover :
      List.Perm
        (canonicalFingerprintRecognizedBlocksCNF leftBlocks)
        f :=
    canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized
      (f := f) rfl hleft
  have hrightCover :
      List.Perm
        (canonicalFingerprintRecognizedBlocksCNF rightBlocks)
        g :=
    canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized
      (f := g) rfl hright
  have hcovered :
      ParityEncoded.DisjointSupport
        (canonicalFingerprintRecognizedBlocksCNF leftBlocks)
        (canonicalFingerprintRecognizedBlocksCNF rightBlocks) :=
    disjointSupport_of_perm hdisjoint hleftCover hrightCover
  have happendDisjoint :
      CanonicalBlocksAppendDisjoint (leftBlocks ++ rightBlocks) :=
    CanonicalBlocksAppendDisjoint.append_of_disjointCovered
      hleftDisjoint hrightDisjoint hcovered
  exact
    semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk
      (f := f ++ g)
      (groups :=
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g)
      (blocks := leftBlocks ++ rightBlocks)
      hgroups
      (ExtractorCompleteness.GroupsRecognized.append hleft hright)
      hsyntactic
      happendDisjoint

/--
Support-disjoint append fragment for the combined semantic/executable surface,
using semantic append/gluing for the emitted block list.  This is the append
counterpart of the relaxed group-recognition bridge: source-level framing is
still required, but block-internal append-disjointness is not.
-/
theorem semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) leftBlocks)
    (hright :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport g) rightBlocks)
    (hleftSyntactic : CanonicalBlocksToSyntacticOk leftBlocks)
    (hrightSyntactic : CanonicalBlocksToSyntacticOk rightBlocks) :
    ExtractorCompleteness.SemanticExtractorCompleteOn (f ++ g)
      (canonicalFingerprintRecognizedBlocksGF2
        (leftBlocks ++ rightBlocks)) := by
  have hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g :=
    GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
      f g hdisjoint hnonempty
  have hsyntactic :
      CanonicalBlocksToSyntacticOk (leftBlocks ++ rightBlocks) :=
    CanonicalBlocksToSyntacticOk.append hleftSyntactic hrightSyntactic
  exact
    semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append
      (f := f ++ g)
      (groups :=
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g)
      (blocks := leftBlocks ++ rightBlocks)
      hgroups
      (ExtractorCompleteness.GroupsRecognized.append hleft hright)
      hsyntactic

/--
Support-disjoint recognized fragments are residual-free for the enhanced
fallback splitter.  This is the enhanced, function-level counterpart of the
baseline append-group-recognition bridge: no same-support fallback branch is
used when both framed fragments are already recognized.
-/
theorem enhancedExtractorCompleteOn_of_disjoint_appendGroupRecognition
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) leftBlocks)
    (hright :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport g) rightBlocks) :
    EnhancedExtractorCompleteOn (f ++ g)
      (canonicalFingerprintRecognizedBlocksGF2
        (leftBlocks ++ rightBlocks)) := by
  have hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g :=
    GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
      f g hdisjoint hnonempty
  exact
    enhancedExtractorCompleteOn_of_groupRecognition
      (f := f ++ g)
      (groups :=
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g)
      (blocks := leftBlocks ++ rightBlocks)
      hgroups
      (ExtractorCompleteness.GroupsRecognized.append hleft hright)
      (List.Perm.refl _)

/--
Support-disjoint recognized fragments satisfy the combined
semantic/enhanced-executable surface when their emitted blocks pass the
executable syntactic upgrade.  This theorem is a recognizer-complete lane for
CNFs not necessarily produced by the generated-family encoder.
-/
theorem enhancedSemanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : GroupFrame.CNFClausesHaveNonemptySupport g)
    (hleft :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) leftBlocks)
    (hright :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport g) rightBlocks)
    (hleftSyntactic : CanonicalBlocksToSyntacticOk leftBlocks)
    (hrightSyntactic : CanonicalBlocksToSyntacticOk rightBlocks) :
    EnhancedSemanticExtractorCompleteOn (f ++ g)
      (canonicalFingerprintRecognizedBlocksGF2
        (leftBlocks ++ rightBlocks)) := by
  have hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g :=
    GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport
      f g hdisjoint hnonempty
  have hsyntactic :
      CanonicalBlocksToSyntacticOk (leftBlocks ++ rightBlocks) :=
    CanonicalBlocksToSyntacticOk.append hleftSyntactic hrightSyntactic
  exact
    enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append
      (f := f ++ g)
      (groups :=
        groupClausesByCanonicalSupport f ++
          groupClausesByCanonicalSupport g)
      (blocks := leftBlocks ++ rightBlocks)
      hgroups
      (ExtractorCompleteness.GroupsRecognized.append hleft hright)
      hsyntactic

/--
Enhanced induction-step bridge for generated parity atoms whose canonical
support key is fresh for the recognized prefix.  This is the production-shaped
fallback-splitter analogue of
`extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint`.
-/
theorem enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint
    {m : Nat}
    {f : CNFModel.CNF m}
    {prefixBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hprefix :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) prefixBlocks)
    (hkeyDisjoint :
      GroupFrame.CNFClauseKeysDisjoint f (clausesForVertex vars charge))
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    EnhancedExtractorCompleteOn
      (f ++ clausesForVertex vars charge)
      (List.append (canonicalFingerprintRecognizedBlocksGF2 prefixBlocks)
        [parityClauseForVertex vars charge]) := by
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf hnormal with
    ⟨block, hinfer, _hsyntactic, hcompact⟩
  have hgroupsRight :
      groupClausesByCanonicalSupport (clausesForVertex vars charge) =
        [(GroupFrame.canonicalSupportKeyForVars vars,
          clausesForVertex vars charge)] :=
    GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
      hcnf
  have hgroupsAppend :
      groupClausesByCanonicalSupport (f ++ clausesForVertex vars charge) =
        groupClausesByCanonicalSupport f ++
          [(GroupFrame.canonicalSupportKeyForVars vars,
            clausesForVertex vars charge)] := by
    have hframe :=
      GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
        f (clausesForVertex vars charge) hkeyDisjoint
    rw [hgroupsRight] at hframe
    exact hframe
  apply enhancedExtractorCompleteOn_of_groupRecognition
    (f := f ++ clausesForVertex vars charge)
    (groups :=
      groupClausesByCanonicalSupport f ++
        [(GroupFrame.canonicalSupportKeyForVars vars,
          clausesForVertex vars charge)])
    (blocks := prefixBlocks ++ [block])
  · exact hgroupsAppend
  · exact
      ExtractorCompleteness.GroupsRecognized.append
        hprefix (And.intro hinfer True.intro)
  · rw [canonicalFingerprintRecognizedBlocksGF2_append]
    simp [canonicalFingerprintRecognizedBlocksGF2, hcompact]

/--
Enhanced induction-step bridge for support-disjoint generated parity atoms.
This wrapper derives the canonical support-key frame from ordinary support
disjointness plus the generated block's nonempty-support side condition.
-/
theorem enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized
    {m : Nat}
    {f : CNFModel.CNF m}
    {prefixBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hprefix :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) prefixBlocks)
    (hdisjoint :
      ParityEncoded.DisjointSupport f (clausesForVertex vars charge))
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hvars : Not (vars = [])) :
    EnhancedExtractorCompleteOn
      (f ++ clausesForVertex vars charge)
      (List.append (canonicalFingerprintRecognizedBlocksGF2 prefixBlocks)
        [parityClauseForVertex vars charge]) := by
  have hnonempty :
      GroupFrame.CNFClausesHaveNonemptySupport
        (clausesForVertex vars charge) :=
    GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex
      (m := m) (vars := vars) (charge := charge) hvars
  exact
    enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint
      hprefix
      (GroupFrame.clauseKeysDisjoint_of_disjointSupport
        f (clausesForVertex vars charge) hdisjoint hnonempty)
      hcnf hnormal

/--
Combined semantic/enhanced induction step for generated parity atoms whose
canonical support key is fresh for the recognized prefix.  The prefix must carry
successful syntactic upgrades for its emitted canonical blocks; the new
generated atom supplies its own syntactic upgrade through the recognizer theorem.
-/
theorem enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint
    {m : Nat}
    {f : CNFModel.CNF m}
    {prefixBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hprefix :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) prefixBlocks)
    (hprefixSyntactic : CanonicalBlocksToSyntacticOk prefixBlocks)
    (hkeyDisjoint :
      GroupFrame.CNFClauseKeysDisjoint f (clausesForVertex vars charge))
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars) :
    EnhancedSemanticExtractorCompleteOn
      (f ++ clausesForVertex vars charge)
      (List.append (canonicalFingerprintRecognizedBlocksGF2 prefixBlocks)
        [parityClauseForVertex vars charge]) := by
  rcases
    inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic
      hcnf hnormal with
    ⟨block, hinfer, hsyntactic, hcompact⟩
  have hgroupsRight :
      groupClausesByCanonicalSupport (clausesForVertex vars charge) =
        [(GroupFrame.canonicalSupportKeyForVars vars,
          clausesForVertex vars charge)] :=
    GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
      hcnf
  have hgroupsAppend :
      groupClausesByCanonicalSupport (f ++ clausesForVertex vars charge) =
        groupClausesByCanonicalSupport f ++
          [(GroupFrame.canonicalSupportKeyForVars vars,
            clausesForVertex vars charge)] := by
    have hframe :=
      GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
        f (clausesForVertex vars charge) hkeyDisjoint
    rw [hgroupsRight] at hframe
    exact hframe
  have hsyntactic :
      CanonicalBlocksToSyntacticOk (prefixBlocks ++ [block]) :=
    CanonicalBlocksToSyntacticOk.append hprefixSyntactic
      (CanonicalBlocksToSyntacticOk.singleton block hsyntactic)
  have hsem :
      EnhancedSemanticExtractorCompleteOn
        (f ++ clausesForVertex vars charge)
        (canonicalFingerprintRecognizedBlocksGF2
          (prefixBlocks ++ [block])) :=
    enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append
      (f := f ++ clausesForVertex vars charge)
      (groups :=
        groupClausesByCanonicalSupport f ++
          [(GroupFrame.canonicalSupportKeyForVars vars,
            clausesForVertex vars charge)])
      (blocks := prefixBlocks ++ [block])
      hgroupsAppend
      (ExtractorCompleteness.GroupsRecognized.append
        hprefix (And.intro hinfer True.intro))
      hsyntactic
  simpa [canonicalFingerprintRecognizedBlocksGF2_append,
    canonicalFingerprintRecognizedBlocksGF2, hcompact] using hsem

/--
Combined semantic/enhanced induction step for support-disjoint generated parity
atoms.  This is the support-disjoint convenience wrapper around the key-fresh
canonical support theorem.
-/
theorem enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized
    {m : Nat}
    {f : CNFModel.CNF m}
    {prefixBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hprefix :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport f) prefixBlocks)
    (hprefixSyntactic : CanonicalBlocksToSyntacticOk prefixBlocks)
    (hdisjoint :
      ParityEncoded.DisjointSupport f (clausesForVertex vars charge))
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : GroupFrame.VarsInCanonicalSupportOrder vars)
    (hvars : Not (vars = [])) :
    EnhancedSemanticExtractorCompleteOn
      (f ++ clausesForVertex vars charge)
      (List.append (canonicalFingerprintRecognizedBlocksGF2 prefixBlocks)
        [parityClauseForVertex vars charge]) := by
  have hnonempty :
      GroupFrame.CNFClausesHaveNonemptySupport
        (clausesForVertex vars charge) :=
    GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex
      (m := m) (vars := vars) (charge := charge) hvars
  exact
    enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint
      hprefix hprefixSyntactic
      (GroupFrame.clauseKeysDisjoint_of_disjointSupport
        f (clausesForVertex vars charge) hdisjoint hnonempty)
      hcnf hnormal

end AtomicClassBridge
end TseitinCNFData
end CertifiedAffine
