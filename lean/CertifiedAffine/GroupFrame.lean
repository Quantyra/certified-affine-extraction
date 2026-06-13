import Mathlib.Data.List.Dedup
import CertifiedAffine.ExtractorCompleteness
import CertifiedAffine.CanonicalSort

/-!
# Canonical Support Grouping Frame Lemmas

This module proves the first structural frame property for the executable
canonical support grouper.  The theorem is intentionally phrased with key
freshness rather than full CNF semantic disjointness: the grouping function only
observes canonical clause-support keys.
-/

namespace CertifiedAffine
namespace TseitinCNFData

namespace GroupFrame

/-- The canonical keys attached to a list of support groups. -/
def groupKeys {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) :
    List CanonicalClauseSupportKey :=
  groups.map Prod.fst

/-- The input clauses whose canonical support key is the selected key. -/
def cnfClausesForKey {m : Nat}
    (key : CanonicalClauseSupportKey)
    (f : CNFModel.CNF m) : CNFModel.CNF m :=
  f.filter (fun c => decide (canonicalClauseSupportKey c = key))

/-- The clauses stored in executable support groups for the selected key. -/
def groupClausesForKey {m : Nat}
    (key : CanonicalClauseSupportKey)
    (groups : List (CanonicalSupportClauseGroup m)) :
    CNFModel.CNF m :=
  (groups.filter (fun g => decide (g.1 = key))).bind Prod.snd

/-- One clause has a key not already present in a support-group list. -/
def ClauseKeyFreshForGroups {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m)) : Prop :=
  Not (List.Mem (canonicalClauseSupportKey c) (groupKeys groups))

/-- Every clause in a CNF has a key not already present in a support-group list. -/
def CNFKeysFreshForGroups {m : Nat}
    (f : CNFModel.CNF m)
    (groups : List (CanonicalSupportClauseGroup m)) : Prop :=
  forall c : CNFModel.Clause m,
    List.Mem c f -> ClauseKeyFreshForGroups c groups

/--
Operational disjointness for the grouping pass: no clause from the right CNF
has the same canonical support key as a clause from the left CNF.
-/
def CNFClauseKeysDisjoint {m : Nat}
    (f g : CNFModel.CNF m) : Prop :=
  forall cf : CNFModel.Clause m,
    List.Mem cf f ->
    forall cg : CNFModel.Clause m,
      List.Mem cg g ->
      Not (canonicalClauseSupportKey cg = canonicalClauseSupportKey cf)

/-- Every clause in a CNF has at least one variable in its support. -/
def CNFClausesHaveNonemptySupport {m : Nat}
    (f : CNFModel.CNF m) : Prop :=
  forall c : CNFModel.Clause m,
    List.Mem c f ->
      exists v : Fin m, List.Mem v (ParityEncoded.clauseSupport c)

/-- Canonical support key determined directly by a variable list. -/
def canonicalSupportKeyForVars {m : Nat}
    (vars : List (Fin m)) : CanonicalClauseSupportKey :=
  (sortFinByVal vars).eraseDups.map (fun v => v.val)

/--
Variable-list normal form expected by exact support inference: sorting by
variable index and deduplicating leaves the list unchanged.
-/
def VarsInCanonicalSupportOrder {m : Nat}
    (vars : List (Fin m)) : Prop :=
  (sortFinByVal vars).eraseDups = vars

/-- Every clause in a CNF has a fixed canonical support key. -/
def CNFClausesHaveCanonicalSupportKey {m : Nat}
    (f : CNFModel.CNF m)
    (key : CanonicalClauseSupportKey) : Prop :=
  forall c : CNFModel.Clause m,
    List.Mem c f -> canonicalClauseSupportKey c = key

/-- Every clause in a CNF has a fixed canonical support-variable list. -/
def CNFClausesHaveCanonicalSupportVars {m : Nat}
    (f : CNFModel.CNF m)
    (vars : List (Fin m)) : Prop :=
  forall c : CNFModel.Clause m,
    List.Mem c f -> canonicalClauseSupportVars c = vars

/-- Every emitted support group stores only clauses whose key is the group key. -/
def SupportGroupsHaveOwnCanonicalSupportKey {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) : Prop :=
  forall g : CanonicalSupportClauseGroup m,
    List.Mem g groups -> CNFClausesHaveCanonicalSupportKey g.2 g.1

/-- Finite lists are determined by their `Fin.val` projection. -/
theorem finList_eq_of_map_val_eq
    {m : Nat}
    {xs ys : List (Fin m)}
    (h : xs.map (fun v => v.val) = ys.map (fun v => v.val)) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          rfl
      | cons y ys =>
          simp at h
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at h
      | cons y ys =>
          simp at h
          cases h with
          | intro hhead htail =>
              have hxy : x = y := Fin.ext hhead
              subst y
              have htailEq : xs = ys := ih htail
              rw [htailEq]

/-- Canonical support keys determine canonical support-variable lists. -/
theorem canonicalClauseSupportVars_eq_of_key_eq
    {m : Nat}
    {c d : CNFModel.Clause m}
    (hkey : canonicalClauseSupportKey c = canonicalClauseSupportKey d) :
    canonicalClauseSupportVars c = canonicalClauseSupportVars d := by
  unfold canonicalClauseSupportKey at hkey
  exact finList_eq_of_map_val_eq hkey

/--
Inserting one clause into support groups preserves the invariant that each
group stores only clauses with its own canonical support key.
-/
theorem supportGroupsHaveOwnCanonicalSupportKey_insertClauseByCanonicalSupport
    {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m))
    (hgroups : SupportGroupsHaveOwnCanonicalSupportKey groups) :
    SupportGroupsHaveOwnCanonicalSupportKey
      (insertClauseByCanonicalSupport c groups) := by
  induction groups with
  | nil =>
      intro g hg d hd
      have hg' :
          List.Mem g [(canonicalClauseSupportKey c, [c])] := by
        simpa [insertClauseByCanonicalSupport] using hg
      cases hg' with
      | head =>
          cases hd with
          | head =>
              rfl
          | tail _ hnil =>
              cases hnil
      | tail _ hnil =>
          cases hnil
  | cons head rest ih =>
      intro g hg d hd
      by_cases hkey : canonicalClauseSupportKey c = head.1
      case pos =>
        have hg' :
            List.Mem g ((head.1, head.2 ++ [c]) :: rest) := by
          simpa [insertClauseByCanonicalSupport, hkey] using hg
        cases hg' with
        | head =>
            cases List.mem_append.1 hd with
            | inl hold =>
                exact
                  hgroups head (List.Mem.head rest) d hold
            | inr hnew =>
                cases hnew with
                | head =>
                    exact hkey
                | tail _ hnil =>
                    cases hnil
        | tail _ htail =>
            exact hgroups g (List.Mem.tail head htail) d hd
      case neg =>
        have hg' :
            List.Mem g
              (head :: insertClauseByCanonicalSupport c rest) := by
          simpa [insertClauseByCanonicalSupport, hkey] using hg
        cases hg' with
        | head =>
            exact hgroups head (List.Mem.head rest) d hd
        | tail _ htail =>
            have hrest :
                SupportGroupsHaveOwnCanonicalSupportKey rest := by
              intro g' hg'
              exact hgroups g' (List.Mem.tail head hg')
            exact ih hrest g htail d hd

/--
Folding clauses into support groups preserves the invariant that each group
stores only clauses with its own canonical support key.
-/
theorem supportGroupsHaveOwnCanonicalSupportKey_fold_insert
    {m : Nat}
    (f : CNFModel.CNF m)
    (groups : List (CanonicalSupportClauseGroup m))
    (hgroups : SupportGroupsHaveOwnCanonicalSupportKey groups) :
    SupportGroupsHaveOwnCanonicalSupportKey
      (f.foldl
        (fun groups c => insertClauseByCanonicalSupport c groups)
        groups) := by
  induction f generalizing groups with
  | nil =>
      exact hgroups
  | cons c _ ih =>
      exact ih (insertClauseByCanonicalSupport c groups)
        (supportGroupsHaveOwnCanonicalSupportKey_insertClauseByCanonicalSupport
          c groups hgroups)

/--
The executable support grouper emits groups whose clauses all have the group's
own canonical support key.
-/
theorem supportGroupsHaveOwnCanonicalSupportKey_groupClausesByCanonicalSupport
    {m : Nat}
    (f : CNFModel.CNF m) :
    SupportGroupsHaveOwnCanonicalSupportKey
      (groupClausesByCanonicalSupport f) := by
  unfold groupClausesByCanonicalSupport
  apply supportGroupsHaveOwnCanonicalSupportKey_fold_insert
  intro g hg
  cases hg

/--
Any support group emitted by the executable grouper stores only clauses with
the group's own canonical support key.
-/
theorem supportGroupClausesHaveCanonicalSupportKey_of_mem_groupClausesByCanonicalSupport
    {m : Nat}
    {f : CNFModel.CNF m}
    {g : CanonicalSupportClauseGroup m}
    (hg : List.Mem g (groupClausesByCanonicalSupport f)) :
    CNFClausesHaveCanonicalSupportKey g.2 g.1 :=
  supportGroupsHaveOwnCanonicalSupportKey_groupClausesByCanonicalSupport f g hg

/--
Canonical support-variable homogeneity is preserved by permuting a CNF whose
clauses already share one canonical support-variable list.
-/
theorem cnfClausesHaveCanonicalSupportVars_of_perm
    {m : Nat}
    {f g : CNFModel.CNF m}
    {vars : List (Fin m)}
    (hperm : List.Perm f g)
    (hvars : CNFClausesHaveCanonicalSupportVars g vars) :
    CNFClausesHaveCanonicalSupportVars f vars := by
  intro c hc
  exact hvars c (hperm.subset hc)

/--
Every nonempty support group emitted by the executable grouper is
support-variable homogeneous, using the head clause's canonical support as the
common support.
-/
theorem supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons
    {m : Nat}
    {f : CNFModel.CNF m}
    {g : CanonicalSupportClauseGroup m}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hg : List.Mem g (groupClausesByCanonicalSupport f))
    (hcnf : g.2 = c :: tail) :
    CNFClausesHaveCanonicalSupportVars g.2 (canonicalClauseSupportVars c) := by
  have hkeys :
      CNFClausesHaveCanonicalSupportKey g.2 g.1 :=
    supportGroupClausesHaveCanonicalSupportKey_of_mem_groupClausesByCanonicalSupport hg
  have hckey : canonicalClauseSupportKey c = g.1 :=
    hkeys c (by rw [hcnf]; exact List.Mem.head tail)
  intro d hd
  have hdkey : canonicalClauseSupportKey d = g.1 :=
    hkeys d hd
  exact
    canonicalClauseSupportVars_eq_of_key_eq
      (hdkey.trans hckey.symm)

/-- Inserting into a sorted list preserves exactly the same membership plus the inserted item. -/
theorem mem_insertSortedBy_iff
    {alpha : Type}
    (le : alpha -> alpha -> Bool)
    [DecidableEq alpha]
    (x y : alpha)
    (xs : List alpha) :
    List.Mem y (insertSortedBy le x xs) <->
      y = x \/ List.Mem y xs := by
  induction xs with
  | nil =>
      constructor
      case mp =>
        intro h
        cases h with
        | head =>
            exact Or.inl rfl
        | tail _ htail =>
            cases htail
      case mpr =>
        intro h
        cases h with
        | inl hy =>
            rw [hy]
            exact List.Mem.head []
        | inr hnil =>
            cases hnil
  | cons z zs ih =>
      by_cases hle : le x z = true
      case pos =>
        constructor
        case mp =>
          intro h
          simp [insertSortedBy, hle] at h
          cases h with
          | head =>
              exact Or.inl rfl
          | tail _ htail =>
              cases htail with
              | head =>
                  exact Or.inr (List.Mem.head zs)
              | tail _ hzs =>
                  exact Or.inr (List.Mem.tail z hzs)
        case mpr =>
          intro h
          simp [insertSortedBy, hle]
          cases h with
          | inl hy =>
              rw [hy]
              exact List.Mem.head (z :: zs)
          | inr hz =>
              cases hz with
              | head =>
                  exact List.Mem.tail x (List.Mem.head zs)
              | tail _ hzs =>
                  exact List.Mem.tail x (List.Mem.tail z hzs)
      case neg =>
        constructor
        case mp =>
          intro h
          simp [insertSortedBy, hle] at h
          cases h with
          | head =>
              exact Or.inr (List.Mem.head zs)
          | tail _ htail =>
              cases (ih.1 htail) with
              | inl hnew =>
                  exact Or.inl hnew
              | inr hzs =>
                  exact Or.inr (List.Mem.tail z hzs)
        case mpr =>
          intro h
          simp [insertSortedBy, hle]
          cases h with
          | inl hnew =>
              exact List.Mem.tail z (ih.2 (Or.inl hnew))
          | inr hz =>
              cases hz with
              | head =>
                  exact List.Mem.head
                    (insertSortedBy le x zs)
              | tail _ hzs =>
                  exact List.Mem.tail z (ih.2 (Or.inr hzs))

/-- The local insertion sort preserves list membership. -/
theorem mem_sortByBool_iff
    {alpha : Type}
    (le : alpha -> alpha -> Bool)
    [DecidableEq alpha]
    (x : alpha)
    (xs : List alpha) :
    List.Mem x (sortByBool le xs) <-> List.Mem x xs := by
  induction xs with
  | nil =>
      simp [sortByBool]
  | cons y ys ih =>
      rw [sortByBool]
      rw [mem_insertSortedBy_iff]
      rw [ih]
      constructor
      case mp =>
        intro h
        cases h with
        | inl hxy =>
            rw [hxy]
            exact List.Mem.head ys
        | inr hxs =>
            exact List.Mem.tail y hxs
      case mpr =>
        intro h
        cases h with
        | head =>
            exact Or.inl rfl
        | tail _ hxs =>
            exact Or.inr hxs

/-- Boolean list membership agrees with propositional membership for lawful equality. -/
theorem elem_eq_true_iff_mem
    {alpha : Type}
    [BEq alpha] [LawfulBEq alpha]
    (x : alpha)
    (xs : List alpha) :
    List.elem x xs = true <-> List.Mem x xs := by
  induction xs with
  | nil =>
      constructor
      case mp =>
        intro h
        cases h
      case mpr =>
        intro h
        cases h
  | cons y ys ih =>
      by_cases hxy : x = y
      case pos =>
        subst y
        constructor
        case mp =>
          intro _h
          exact List.Mem.head ys
        case mpr =>
          intro _h
          simp [List.elem_cons, beq_self_eq_true]
      case neg =>
        have hbeq : (x == y) = false := by
          cases heq : (x == y) with
          | false =>
              rfl
          | true =>
              have hxyeq : x = y := (beq_iff_eq).1 heq
              exact False.elim (hxy hxyeq)
        rw [List.elem_cons, hbeq]
        constructor
        case mp =>
          intro h
          exact List.Mem.tail y ((ih).1 h)
        case mpr =>
          intro h
          cases h with
          | head =>
              exact False.elim (hxy rfl)
          | tail _ htail =>
              exact (ih).2 htail

/-- The implementation loop behind `eraseDups` preserves membership from input or accumulator. -/
theorem mem_eraseDups_loop_iff
    {alpha : Type}
    [BEq alpha] [LawfulBEq alpha]
    (x : alpha)
    (xs acc : List alpha) :
    List.Mem x (List.eraseDups.loop xs acc) <->
      List.Mem x xs \/ List.Mem x acc := by
  induction xs generalizing acc with
  | nil =>
      constructor
      case mp =>
        intro h
        exact Or.inr (List.mem_reverse.1 h)
      case mpr =>
        intro h
        cases h with
        | inl hnil =>
            cases hnil
        | inr hacc =>
            exact List.mem_reverse.2 hacc
  | cons a xs ih =>
      by_cases ha : List.Mem a acc
      case pos =>
        have helem : List.elem a acc = true :=
          (elem_eq_true_iff_mem a acc).2 ha
        simp only [List.eraseDups.loop, helem]
        rw [ih]
        constructor
        case mp =>
          intro h
          cases h with
          | inl hxs =>
              exact Or.inl (List.Mem.tail a hxs)
          | inr hacc =>
              exact Or.inr hacc
        case mpr =>
          intro h
          cases h with
          | inl hleft =>
              cases hleft with
              | head =>
                  exact Or.inr ha
              | tail _ hxs =>
                  exact Or.inl hxs
          | inr hacc =>
              exact Or.inr hacc
      case neg =>
        have helem : List.elem a acc = false := by
          cases heq : List.elem a acc with
          | false =>
              rfl
          | true =>
              have hmem := (elem_eq_true_iff_mem a acc).1 heq
              exact False.elim (ha hmem)
        simp only [List.eraseDups.loop, helem]
        rw [ih]
        constructor
        case mp =>
          intro h
          cases h with
          | inl hxs =>
              exact Or.inl (List.Mem.tail a hxs)
          | inr hmem =>
              cases hmem with
              | head =>
                  exact Or.inl (List.Mem.head xs)
              | tail _ hacc =>
                  exact Or.inr hacc
        case mpr =>
          intro h
          cases h with
          | inl hleft =>
              cases hleft with
              | head =>
                  exact Or.inr (List.Mem.head acc)
              | tail _ hxs =>
                  exact Or.inl hxs
          | inr hacc =>
              exact Or.inr (List.Mem.tail a hacc)

/-- `eraseDups` preserves list membership for lawful equality. -/
theorem mem_eraseDups_iff
    {alpha : Type}
    [BEq alpha] [LawfulBEq alpha]
    (x : alpha)
    (xs : List alpha) :
    List.Mem x (List.eraseDups xs) <-> List.Mem x xs := by
  have hloop :=
    mem_eraseDups_loop_iff x xs ([] : List alpha)
  unfold List.eraseDups
  constructor
  case mp =>
    intro h
    cases hloop.1 h with
    | inl hxs =>
        exact hxs
    | inr hnil =>
        cases hnil
  case mpr =>
    intro h
    exact hloop.2 (Or.inl h)

/-- Canonical clause-support variables are exactly the ordinary clause support. -/
theorem mem_canonicalClauseSupportVars_iff
    {m : Nat}
    (c : CNFModel.Clause m)
    (v : Fin m) :
    List.Mem v (canonicalClauseSupportVars c) <->
      List.Mem v (ParityEncoded.clauseSupport c) := by
  unfold canonicalClauseSupportVars ParityEncoded.clauseSupport sortFinByVal
  rw [mem_eraseDups_iff]
  exact mem_sortByBool_iff
    (fun a b : Fin m => decide (a.val <= b.val))
    v (c.map (fun l => l.var))

/-- Canonical clause-support keys are exactly the values of ordinary support variables. -/
theorem mem_canonicalClauseSupportKey_iff
    {m : Nat}
    (c : CNFModel.Clause m)
    (key : Nat) :
    List.Mem key (canonicalClauseSupportKey c) <->
      exists v : Fin m,
        List.Mem v (ParityEncoded.clauseSupport c) /\
          v.val = key := by
  constructor
  case mp =>
    intro hmem
    unfold canonicalClauseSupportKey at hmem
    cases List.mem_map.1 hmem with
    | intro v hvAnd =>
        cases hvAnd with
        | intro hv hval =>
            exact
              Exists.intro v
                (And.intro
                  ((mem_canonicalClauseSupportVars_iff c v).1 hv)
                  hval)
  case mpr =>
    intro hmem
    cases hmem with
    | intro v hvAnd =>
        cases hvAnd with
        | intro hv hval =>
            unfold canonicalClauseSupportKey
            exact
              List.mem_map.2
                (Exists.intro v
                  (And.intro
                    ((mem_canonicalClauseSupportVars_iff c v).2 hv)
                    hval))

/-- Ordinary variable-disjoint support implies operational clause-key disjointness. -/
theorem clauseKeysDisjoint_of_disjointSupport
    {m : Nat}
    (f g : CNFModel.CNF m)
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : CNFClausesHaveNonemptySupport g) :
    CNFClauseKeysDisjoint f g := by
  intro cf hcf cg hcg hkey
  have hgNonempty := hnonempty cg hcg
  cases hgNonempty with
  | intro vg hvg =>
      have hkeyCg :
          List.Mem vg.val (canonicalClauseSupportKey cg) :=
        (mem_canonicalClauseSupportKey_iff cg vg.val).2
          (Exists.intro vg (And.intro hvg rfl))
      have hkeyCf :
          List.Mem vg.val (canonicalClauseSupportKey cf) := by
        simpa [hkey] using hkeyCg
      have hcfSupport :=
        (mem_canonicalClauseSupportKey_iff cf vg.val).1 hkeyCf
      cases hcfSupport with
      | intro vf hvfAnd =>
          cases hvfAnd with
          | intro hvf hval =>
              have hvEq : vf = vg := Fin.ext hval
              have hfCnf :
                  List.Mem vg (ParityEncoded.cnfSupport f) := by
                unfold ParityEncoded.cnfSupport
                exact
                  List.mem_bind.2
                    (Exists.intro cf
                      (And.intro hcf (by simpa [hvEq] using hvf)))
              have hgCnf :
                  List.Mem vg (ParityEncoded.cnfSupport g) := by
                unfold ParityEncoded.cnfSupport
                exact
                  List.mem_bind.2
                    (Exists.intro cg (And.intro hcg hvg))
              exact hdisjoint vg hfCnf hgCnf

/--
Inserting a fresh-key clause into an appended group list cannot alter the left
frame; insertion is pushed into the right side.
-/
theorem insertClauseByCanonicalSupport_append_of_fresh
    {m : Nat}
    (c : CNFModel.Clause m)
    (groups rest : List (CanonicalSupportClauseGroup m))
    (hfresh : ClauseKeyFreshForGroups c groups) :
    insertClauseByCanonicalSupport c (groups ++ rest) =
      groups ++ insertClauseByCanonicalSupport c rest := by
  induction groups with
  | nil =>
      rfl
  | cons g groups ih =>
      have hneq : Not (canonicalClauseSupportKey c = g.1) := by
        intro h
        apply hfresh
        unfold groupKeys
        simpa [h] using
          (List.Mem.head
            (List.map Prod.fst groups) :
            List.Mem g.1 (g.1 :: List.map Prod.fst groups))
      have htail : ClauseKeyFreshForGroups c groups := by
        intro hmem
        apply hfresh
        unfold groupKeys at hmem
        unfold groupKeys
        exact List.Mem.tail g.1 hmem
      simp [insertClauseByCanonicalSupport, hneq, ih htail]

/--
Folding fresh-key suffix clauses over an appended accumulator preserves the
left frame exactly.
-/
theorem fold_insert_append_of_fresh
    {m : Nat}
    (suffix : CNFModel.CNF m)
    (prefixGroups suffixGroups : List (CanonicalSupportClauseGroup m))
    (hfresh : CNFKeysFreshForGroups suffix prefixGroups) :
    suffix.foldl
        (fun groups c => insertClauseByCanonicalSupport c groups)
        (prefixGroups ++ suffixGroups) =
      prefixGroups ++
        suffix.foldl
          (fun groups c => insertClauseByCanonicalSupport c groups)
          suffixGroups := by
  induction suffix generalizing suffixGroups with
  | nil =>
      rfl
  | cons c suffix ih =>
      have hcFresh : ClauseKeyFreshForGroups c prefixGroups :=
        hfresh c (List.Mem.head suffix)
      have hsuffixFresh : CNFKeysFreshForGroups suffix prefixGroups := by
        intro d hd
        exact hfresh d (List.Mem.tail c hd)
      calc
        (c :: suffix).foldl
            (fun groups d => insertClauseByCanonicalSupport d groups)
            (prefixGroups ++ suffixGroups)
            =
          suffix.foldl
            (fun groups d => insertClauseByCanonicalSupport d groups)
            (insertClauseByCanonicalSupport c
              (prefixGroups ++ suffixGroups)) := by
              rfl
        _ =
          suffix.foldl
            (fun groups d => insertClauseByCanonicalSupport d groups)
            (prefixGroups ++
              insertClauseByCanonicalSupport c suffixGroups) := by
              rw [insertClauseByCanonicalSupport_append_of_fresh
                c prefixGroups suffixGroups hcFresh]
        _ =
          prefixGroups ++
            suffix.foldl
              (fun groups d => insertClauseByCanonicalSupport d groups)
              (insertClauseByCanonicalSupport c suffixGroups) :=
              ih (insertClauseByCanonicalSupport c suffixGroups)
                hsuffixFresh
        _ =
          prefixGroups ++
            (c :: suffix).foldl
              (fun groups d => insertClauseByCanonicalSupport d groups)
              suffixGroups := by
              rfl

/--
Grouping commutes with append when every suffix clause has a canonical support
key fresh for the prefix's already-computed support groups.
-/
theorem groupClausesByCanonicalSupport_append_of_fresh
    {m : Nat}
    (f g : CNFModel.CNF m)
    (hfresh :
      CNFKeysFreshForGroups g (groupClausesByCanonicalSupport f)) :
    groupClausesByCanonicalSupport (f ++ g) =
      groupClausesByCanonicalSupport f ++
        groupClausesByCanonicalSupport g := by
  unfold groupClausesByCanonicalSupport
  rw [List.foldl_append]
  simpa using fold_insert_append_of_fresh g
    (f.foldl (fun groups c => insertClauseByCanonicalSupport c groups) [])
    [] hfresh

/--
Folding clauses whose canonical support key is already the accumulator's only
key appends those clauses to that single group.
-/
theorem fold_insert_same_key_single
    {m : Nat}
    {key : CanonicalClauseSupportKey}
    (tail acc : CNFModel.CNF m)
    (hkeys :
      forall c : CNFModel.Clause m,
        List.Mem c tail -> canonicalClauseSupportKey c = key) :
    tail.foldl
        (fun groups c => insertClauseByCanonicalSupport c groups)
        [(key, acc)] =
      [(key, acc ++ tail)] := by
  induction tail generalizing acc with
  | nil =>
      simp
  | cons c tail ih =>
      have hc : canonicalClauseSupportKey c = key :=
        hkeys c (List.Mem.head tail)
      have htail :
          forall d : CNFModel.Clause m,
            List.Mem d tail -> canonicalClauseSupportKey d = key := by
        intro d hd
        exact hkeys d (List.Mem.tail c hd)
      calc
        (c :: tail).foldl
            (fun groups d => insertClauseByCanonicalSupport d groups)
            [(key, acc)]
            =
          tail.foldl
            (fun groups d => insertClauseByCanonicalSupport d groups)
            (insertClauseByCanonicalSupport c [(key, acc)]) := by
              rfl
        _ =
          tail.foldl
            (fun groups d => insertClauseByCanonicalSupport d groups)
            [(key, acc ++ [c])] := by
              simp [insertClauseByCanonicalSupport, hc]
        _ = [(key, (acc ++ [c]) ++ tail)] :=
          ih (acc ++ [c]) htail
        _ = [(key, acc ++ c :: tail)] := by
          simp [List.append_assoc]

/--
If every clause in a nonempty CNF has the same canonical support key, the
executable canonical support grouper returns one group covering the original
CNF in order.
-/
theorem groupClausesByCanonicalSupport_cons_eq_single_of_same_key
    {m : Nat}
    {key : CanonicalClauseSupportKey}
    (c : CNFModel.Clause m)
    (tail : CNFModel.CNF m)
    (hhead : canonicalClauseSupportKey c = key)
    (htail :
      forall d : CNFModel.Clause m,
        List.Mem d tail -> canonicalClauseSupportKey d = key) :
    groupClausesByCanonicalSupport (c :: tail) =
      [(key, c :: tail)] := by
  unfold groupClausesByCanonicalSupport
  change
    tail.foldl
        (fun groups d => insertClauseByCanonicalSupport d groups)
        (insertClauseByCanonicalSupport c []) =
      [(key, c :: tail)]
  simp [insertClauseByCanonicalSupport, hhead]
  simpa using
    fold_insert_same_key_single
      (tail := tail) (acc := [c]) htail

/--
Canonical support-key uniformity is preserved when the ordinary CNF clause list
is permuted.
-/
theorem cnfClausesHaveCanonicalSupportKey_of_perm
    {m : Nat}
    {f g : CNFModel.CNF m}
    {key : CanonicalClauseSupportKey}
    (hperm : List.Perm f g)
    (hkeys : CNFClausesHaveCanonicalSupportKey g key) :
    CNFClausesHaveCanonicalSupportKey f key := by
  intro c hc
  exact hkeys c (hperm.subset hc)

/-- Clause-key disjointness is preserved by permuting the left CNF. -/
theorem cnfClauseKeysDisjoint_of_perm_left
    {m : Nat}
    {f f' g : CNFModel.CNF m}
    (hperm : List.Perm f' f)
    (hdisjoint : CNFClauseKeysDisjoint f g) :
    CNFClauseKeysDisjoint f' g := by
  intro cf hcf cg hcg hkey
  exact hdisjoint cf (hperm.subset hcf) cg hcg hkey

/-- Clause-key disjointness is preserved by permuting the right CNF. -/
theorem cnfClauseKeysDisjoint_of_perm_right
    {m : Nat}
    {f g g' : CNFModel.CNF m}
    (hperm : List.Perm g' g)
    (hdisjoint : CNFClauseKeysDisjoint f g) :
    CNFClauseKeysDisjoint f g' := by
  intro cf hcf cg hcg hkey
  exact hdisjoint cf hcf cg (hperm.subset hcg) hkey

/-- Clause-key disjointness is preserved by permuting both CNFs. -/
theorem cnfClauseKeysDisjoint_of_perm
    {m : Nat}
    {f f' g g' : CNFModel.CNF m}
    (hfperm : List.Perm f' f)
    (hgperm : List.Perm g' g)
    (hdisjoint : CNFClauseKeysDisjoint f g) :
    CNFClauseKeysDisjoint f' g' :=
  cnfClauseKeysDisjoint_of_perm_right hgperm
    (cnfClauseKeysDisjoint_of_perm_left hfperm hdisjoint)

/-- Clause-key disjointness is symmetric. -/
theorem cnfClauseKeysDisjoint_symm
    {m : Nat}
    {f g : CNFModel.CNF m}
    (hdisjoint : CNFClauseKeysDisjoint f g) :
    CNFClauseKeysDisjoint g f := by
  intro cg hcg cf hcf hkey
  exact hdisjoint cf hcf cg hcg hkey.symm

/-- The nonempty-support side condition is preserved by CNF permutation. -/
theorem cnfClausesHaveNonemptySupport_of_perm
    {m : Nat}
    {f f' : CNFModel.CNF m}
    (hperm : List.Perm f' f)
    (hnonempty : CNFClausesHaveNonemptySupport f) :
    CNFClausesHaveNonemptySupport f' := by
  intro c hc
  exact hnonempty c (hperm.subset hc)

/-- Length-matching assignment clauses mention exactly the requested variables. -/
theorem clauseSupport_clauseForAssignment_of_length
    {m : Nat}
    {vars : List (Fin m)}
    {bs : List Bool}
    (hlen : bs.length = vars.length) :
    ParityEncoded.clauseSupport
      (clauseForAssignment vars bs) = vars := by
  induction vars generalizing bs with
  | nil =>
      cases bs with
      | nil =>
          rfl
      | cons _ _ =>
          cases hlen
  | cons v vs ih =>
      cases bs with
      | nil =>
          cases hlen
      | cons b bs =>
          have htail : bs.length = vs.length := Nat.succ.inj hlen
          simp [ParityEncoded.clauseSupport, clauseForAssignment]
          exact ih htail

/-- A length-matching assignment clause has the canonicalized support of `vars`. -/
theorem canonicalClauseSupportVars_clauseForAssignment_of_length
    {m : Nat}
    {vars : List (Fin m)}
    {bs : List Bool}
    (hlen : bs.length = vars.length) :
    canonicalClauseSupportVars (clauseForAssignment vars bs) =
      (sortFinByVal vars).eraseDups := by
  have hsupport :=
    clauseSupport_clauseForAssignment_of_length
      (m := m) (vars := vars) (bs := bs) hlen
  unfold ParityEncoded.clauseSupport at hsupport
  unfold canonicalClauseSupportVars
  rw [hsupport]

/--
The canonical support key of a length-matching assignment clause depends only
on the variable list, not on the Boolean row.
-/
theorem canonicalClauseSupportKey_clauseForAssignment_of_length
    {m : Nat}
    {vars : List (Fin m)}
    {bs : List Bool}
    (hlen : bs.length = vars.length) :
    canonicalClauseSupportKey (clauseForAssignment vars bs) =
      canonicalSupportKeyForVars vars := by
  have hsupport :=
    clauseSupport_clauseForAssignment_of_length
      (m := m) (vars := vars) (bs := bs) hlen
  unfold ParityEncoded.clauseSupport at hsupport
  unfold canonicalClauseSupportKey canonicalClauseSupportVars
    canonicalSupportKeyForVars
  rw [hsupport]

/--
The inline fold used by `clausesForVertex` preserves the fact that every
generated clause has the canonical support-variable list induced by `vars`.
-/
theorem cnfClausesHaveCanonicalSupportVars_foldl_clausesForVertex
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    (rows : List (List Bool))
    (acc : CNFModel.CNF m)
    (hrows :
      forall bs : List Bool,
        List.Mem bs rows -> bs.length = vars.length)
    (hacc :
      CNFClausesHaveCanonicalSupportVars acc
        ((sortFinByVal vars).eraseDups)) :
    CNFClausesHaveCanonicalSupportVars
      (rows.foldl
        (fun acc bs =>
          if (parity bs == charge) = true then
            acc
          else
            acc ++ [clauseForAssignment vars bs])
        acc)
      ((sortFinByVal vars).eraseDups) := by
  induction rows generalizing acc with
  | nil =>
      exact hacc
  | cons row rows ih =>
      have htailRows :
          forall bs : List Bool,
            List.Mem bs rows -> bs.length = vars.length := by
        intro bs hbs
        exact hrows bs (List.Mem.tail row hbs)
      have hrowLen : row.length = vars.length :=
        hrows row (List.Mem.head rows)
      by_cases hgood : (parity row == charge) = true
      case pos =>
        change
          CNFClausesHaveCanonicalSupportVars
            (rows.foldl
              (fun acc bs =>
                if (parity bs == charge) = true then
                  acc
                else
                  acc ++ [clauseForAssignment vars bs])
              (if (parity row == charge) = true then
                acc
              else
                acc ++ [clauseForAssignment vars row]))
            ((sortFinByVal vars).eraseDups)
        rw [if_pos hgood]
        exact ih acc htailRows hacc
      case neg =>
        change
          CNFClausesHaveCanonicalSupportVars
            (rows.foldl
              (fun acc bs =>
                if (parity bs == charge) = true then
                  acc
                else
                  acc ++ [clauseForAssignment vars bs])
              (if (parity row == charge) = true then
                acc
              else
                acc ++ [clauseForAssignment vars row]))
            ((sortFinByVal vars).eraseDups)
        rw [if_neg hgood]
        apply ih
        case hrows =>
          exact htailRows
        case hacc =>
          intro c hc
          cases List.mem_append.1 hc with
          | inl hleft =>
              exact hacc c hleft
          | inr hright =>
              cases hright with
              | head =>
                  exact
                    canonicalClauseSupportVars_clauseForAssignment_of_length
                      hrowLen
              | tail _ hnil =>
                  cases hnil

/-- Clause-complete parity expansions have one canonical support-variable list. -/
theorem cnfClausesHaveCanonicalSupportVars_clausesForVertex
    {m : Nat}
    (vars : List (Fin m))
    (charge : Bool) :
    CNFClausesHaveCanonicalSupportVars
      (clausesForVertex vars charge)
      ((sortFinByVal vars).eraseDups) := by
  unfold clausesForVertex
  apply cnfClausesHaveCanonicalSupportVars_foldl_clausesForVertex
  case hrows =>
    intro bs hbs
    exact length_of_mem_allAssignments hbs
  case hacc =>
    intro c hc
    cases hc

/--
The inline fold used by `clausesForVertex` preserves the fact that every
generated clause has the canonical support key induced by `vars`.
-/
theorem cnfClausesHaveCanonicalSupportKey_foldl_clausesForVertex
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    (rows : List (List Bool))
    (acc : CNFModel.CNF m)
    (hrows :
      forall bs : List Bool,
        List.Mem bs rows -> bs.length = vars.length)
    (hacc :
      CNFClausesHaveCanonicalSupportKey acc
        (canonicalSupportKeyForVars vars)) :
    CNFClausesHaveCanonicalSupportKey
      (rows.foldl
        (fun acc bs =>
          if (parity bs == charge) = true then
            acc
          else
            acc ++ [clauseForAssignment vars bs])
        acc)
      (canonicalSupportKeyForVars vars) := by
  induction rows generalizing acc with
  | nil =>
      exact hacc
  | cons row rows ih =>
      have htailRows :
          forall bs : List Bool,
            List.Mem bs rows -> bs.length = vars.length := by
        intro bs hbs
        exact hrows bs (List.Mem.tail row hbs)
      have hrowLen : row.length = vars.length :=
        hrows row (List.Mem.head rows)
      by_cases hgood : (parity row == charge) = true
      case pos =>
        change
          CNFClausesHaveCanonicalSupportKey
            (rows.foldl
              (fun acc bs =>
                if (parity bs == charge) = true then
                  acc
                else
                  acc ++ [clauseForAssignment vars bs])
              (if (parity row == charge) = true then
                acc
              else
                acc ++ [clauseForAssignment vars row]))
            (canonicalSupportKeyForVars vars)
        rw [if_pos hgood]
        exact ih acc htailRows hacc
      case neg =>
        change
          CNFClausesHaveCanonicalSupportKey
            (rows.foldl
              (fun acc bs =>
                if (parity bs == charge) = true then
                  acc
                else
                  acc ++ [clauseForAssignment vars bs])
              (if (parity row == charge) = true then
                acc
              else
                acc ++ [clauseForAssignment vars row]))
            (canonicalSupportKeyForVars vars)
        rw [if_neg hgood]
        apply ih
        case hrows =>
          exact htailRows
        case hacc =>
          intro c hc
          cases List.mem_append.1 hc with
          | inl hleft =>
              exact hacc c hleft
          | inr hright =>
              cases hright with
              | head =>
                  exact
                    canonicalClauseSupportKey_clauseForAssignment_of_length
                      hrowLen
              | tail _ hnil =>
                  cases hnil

/-- Clause-complete parity expansions have one canonical support key. -/
theorem cnfClausesHaveCanonicalSupportKey_clausesForVertex
    {m : Nat}
    (vars : List (Fin m))
    (charge : Bool) :
    CNFClausesHaveCanonicalSupportKey
      (clausesForVertex vars charge)
      (canonicalSupportKeyForVars vars) := by
  unfold clausesForVertex
  apply cnfClausesHaveCanonicalSupportKey_foldl_clausesForVertex
  case hrows =>
    intro bs hbs
    exact length_of_mem_allAssignments hbs
  case hacc =>
    intro c hc
    cases hc

/--
Any nonempty clause permutation of a generated parity expansion still groups
as one canonical support component.
-/
theorem groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail) :
    groupClausesByCanonicalSupport f =
      [(canonicalSupportKeyForVars vars, f)] := by
  have hall :
      CNFClausesHaveCanonicalSupportKey f
        (canonicalSupportKeyForVars vars) :=
    cnfClausesHaveCanonicalSupportKey_of_perm hperm
      (cnfClausesHaveCanonicalSupportKey_clausesForVertex
        (m := m) vars charge)
  rw [hf]
  apply groupClausesByCanonicalSupport_cons_eq_single_of_same_key
  case hhead =>
    exact hall c (by rw [hf]; exact List.Mem.head tail)
  case htail =>
    intro d hd
    exact hall d (by rw [hf]; exact List.Mem.tail c hd)

/--
The first-clause canonical support inferred from any nonempty clause
permutation of a generated parity expansion is the generated variable list,
provided that list is already in canonical support order.
-/
theorem parityCandidateCanonicalSupportFromBlock_eq_of_perm_clausesForVertex_normal
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hperm : List.Perm f (clausesForVertex vars charge))
    (hf : f = c :: tail)
    (hnormal : VarsInCanonicalSupportOrder vars) :
    parityCandidateCanonicalSupportFromBlock f = vars := by
  have hall : CNFClausesHaveCanonicalSupportVars f vars := by
    intro d hd
    have hgenerated :
        CNFClausesHaveCanonicalSupportVars
          (clausesForVertex vars charge)
          ((sortFinByVal vars).eraseDups) :=
      cnfClausesHaveCanonicalSupportVars_clausesForVertex
        (m := m) vars charge
    have hdtarget : List.Mem d (clausesForVertex vars charge) :=
      hperm.subset hd
    exact (hgenerated d hdtarget).trans hnormal
  simpa [parityCandidateCanonicalSupportFromBlock, hf] using
    hall c (by rw [hf]; exact List.Mem.head tail)

/--
When a generated parity expansion is nonempty, the executable support grouper
returns exactly one canonical support group for it.
-/
theorem groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail) :
    groupClausesByCanonicalSupport (clausesForVertex vars charge) =
      [(canonicalSupportKeyForVars vars, clausesForVertex vars charge)] := by
  have hall :=
    cnfClausesHaveCanonicalSupportKey_clausesForVertex
      (m := m) vars charge
  rw [hcnf]
  apply groupClausesByCanonicalSupport_cons_eq_single_of_same_key
  case hhead =>
    exact hall c (by rw [hcnf]; exact List.Mem.head tail)
  case htail =>
    intro d hd
    exact hall d (by rw [hcnf]; exact List.Mem.tail c hd)

/--
For any nonempty generated parity expansion, support inference from the first
clause recovers the canonicalized generator support.
-/
theorem parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail) :
    parityCandidateCanonicalSupportFromBlock
        (clausesForVertex vars charge) =
      (sortFinByVal vars).eraseDups := by
  have hall :=
    cnfClausesHaveCanonicalSupportVars_clausesForVertex
      (m := m) vars charge
  simpa [parityCandidateCanonicalSupportFromBlock, hcnf] using
    hall c (by rw [hcnf]; exact List.Mem.head tail)

/--
If the generator variable list is already canonical support order, support
inference from a nonempty generated parity expansion recovers that exact list.
-/
theorem parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hcnf : clausesForVertex vars charge = c :: tail)
    (hnormal : VarsInCanonicalSupportOrder vars) :
    parityCandidateCanonicalSupportFromBlock
        (clausesForVertex vars charge) = vars := by
  have hcandidate :=
    parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons
      (m := m) (vars := vars) (charge := charge) hcnf
  unfold VarsInCanonicalSupportOrder at hnormal
  rw [hcandidate, hnormal]

/--
If every clause in a nonempty block has the same canonical support-variable
list, then first-clause support inference recovers that list.
-/
theorem parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons
    {m : Nat}
    {f : CNFModel.CNF m}
    {vars : List (Fin m)}
    {c : CNFModel.Clause m}
    {tail : CNFModel.CNF m}
    (hall : CNFClausesHaveCanonicalSupportVars f vars)
    (hf : f = c :: tail) :
    parityCandidateCanonicalSupportFromBlock f = vars := by
  simpa [parityCandidateCanonicalSupportFromBlock, hf] using
    hall c (by rw [hf]; exact List.Mem.head tail)

/--
Two nonempty support-homogeneous blocks with the same support-variable list
infer the same fixed-charge candidate parity spec.
-/
theorem inferredCanonicalParityBlockSpec_eq_of_supportVars_cons
    {m : Nat}
    {f g : CNFModel.CNF m}
    {vars : List (Fin m)}
    {cf cg : CNFModel.Clause m}
    {ftail gtail : CNFModel.CNF m}
    (hfvars : CNFClausesHaveCanonicalSupportVars f vars)
    (hgvars : CNFClausesHaveCanonicalSupportVars g vars)
    (hf : f = cf :: ftail)
    (hg : g = cg :: gtail)
    (charge : Bool) :
    inferredCanonicalParityBlockSpec f charge =
      inferredCanonicalParityBlockSpec g charge := by
  have hfsupport :
      parityCandidateCanonicalSupportFromBlock f = vars :=
    parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons
      hfvars hf
  have hgsupport :
      parityCandidateCanonicalSupportFromBlock g = vars :=
    parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons
      hgvars hg
  unfold inferredCanonicalParityBlockSpec
  rw [hfsupport, hgsupport]

/--
If candidate support inference is stable across a clause permutation, then a
fixed-charge recognizer miss is stable across that permutation.
-/
theorem inferCanonicalParityBlockWithCharge_eq_none_of_perm_of_inferredSpec_eq
    {m : Nat}
    {f g : CNFModel.CNF m}
    {charge : Bool}
    (hperm : List.Perm g f)
    (hspec :
      inferredCanonicalParityBlockSpec g charge =
        inferredCanonicalParityBlockSpec f charge)
    (hnone : inferCanonicalParityBlockWithCharge f charge = none) :
    inferCanonicalParityBlockWithCharge g charge = none := by
  unfold inferCanonicalParityBlockWithCharge at hnone
  unfold inferCanonicalParityBlockWithCharge
  have hsignal :
      canonicalParityBlockRecognitionSignal g
          (inferredCanonicalParityBlockSpec g charge) =
        canonicalParityBlockRecognitionSignal f
          (inferredCanonicalParityBlockSpec f charge) := by
    rw [hspec]
    exact
      canonicalParityBlockRecognitionSignal_eq_of_block_perm
        (inferredCanonicalParityBlockSpec f charge) hperm
  by_cases hfSignal :
      canonicalParityBlockRecognitionSignal f
        (inferredCanonicalParityBlockSpec f charge) = true
  · simp [hfSignal] at hnone
  · have hgSignal :
        Not
          (canonicalParityBlockRecognitionSignal g
            (inferredCanonicalParityBlockSpec g charge) = true) := by
      intro htrue
      exact hfSignal (by rwa [hsignal] at htrue)
    simp [hgSignal]

/--
If candidate support inference is stable across a clause permutation, then a
fixed-charge recognizer hit transports across that permutation.  The emitted
block changes its stored `blockCNF`, so the conclusion records block-content
permutation rather than option equality.
-/
theorem inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_inferredSpec_eq
    {m : Nat}
    {f g : CNFModel.CNF m}
    {charge : Bool}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm g f)
    (hspec :
      inferredCanonicalParityBlockSpec g charge =
        inferredCanonicalParityBlockSpec f charge)
    (hinfer : inferCanonicalParityBlockWithCharge f charge = some b) :
    exists b' : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlockWithCharge g charge = some b' /\
        b'.spec = b.spec /\
          List.Perm b'.blockCNF b.blockCNF := by
  unfold inferCanonicalParityBlockWithCharge at hinfer
  by_cases hfSignal :
      canonicalParityBlockRecognitionSignal f
        (inferredCanonicalParityBlockSpec f charge) = true
  · simp [hfSignal] at hinfer
    cases hinfer
    have hgSignal :
        canonicalParityBlockRecognitionSignal g
          (inferredCanonicalParityBlockSpec g charge) = true := by
      have hsignal :
          canonicalParityBlockRecognitionSignal g
              (inferredCanonicalParityBlockSpec g charge) =
            canonicalParityBlockRecognitionSignal f
              (inferredCanonicalParityBlockSpec f charge) := by
        rw [hspec]
        exact
          canonicalParityBlockRecognitionSignal_eq_of_block_perm
            (inferredCanonicalParityBlockSpec f charge) hperm
      rw [hsignal, hfSignal]
    let b' : CanonicalFingerprintRecognizedParityBlock m :=
      { blockCNF := g
        spec := inferredCanonicalParityBlockSpec g charge
        fingerprintSignal := hgSignal }
    refine ⟨b', ?_, ?_, ?_⟩
    · unfold inferCanonicalParityBlockWithCharge
      simp [hgSignal, b']
    · simp [b', hspec]
    · simpa [b'] using hperm
  · simp [hfSignal] at hinfer

/--
For nonempty blocks whose clauses all share the same canonical support-variable
list, fixed-charge recognizer hits transport across clause permutation.
-/
theorem inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_supportVars_cons
    {m : Nat}
    {f g : CNFModel.CNF m}
    {vars : List (Fin m)}
    {cf cg : CNFModel.Clause m}
    {ftail gtail : CNFModel.CNF m}
    {charge : Bool}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm g f)
    (hfvars : CNFClausesHaveCanonicalSupportVars f vars)
    (hgvars : CNFClausesHaveCanonicalSupportVars g vars)
    (hf : f = cf :: ftail)
    (hg : g = cg :: gtail)
    (hinfer : inferCanonicalParityBlockWithCharge f charge = some b) :
    exists b' : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlockWithCharge g charge = some b' /\
        b'.spec = b.spec /\
          List.Perm b'.blockCNF b.blockCNF := by
  apply
    inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_inferredSpec_eq
      hperm
  · exact
      (inferredCanonicalParityBlockSpec_eq_of_supportVars_cons
        hfvars hgvars hf hg charge).symm
  · exact hinfer

/--
For nonempty blocks whose clauses all share the same canonical support-variable
list, the public false-first recognizer transports hits across clause
permutation.
-/
theorem inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons
    {m : Nat}
    {f g : CNFModel.CNF m}
    {vars : List (Fin m)}
    {cf cg : CNFModel.Clause m}
    {ftail gtail : CNFModel.CNF m}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    (hperm : List.Perm g f)
    (hfvars : CNFClausesHaveCanonicalSupportVars f vars)
    (hgvars : CNFClausesHaveCanonicalSupportVars g vars)
    (hf : f = cf :: ftail)
    (hg : g = cg :: gtail)
    (hinfer : inferCanonicalParityBlock f = some b) :
    exists b' : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock g = some b' /\
        b'.spec = b.spec /\
          List.Perm b'.blockCNF b.blockCNF := by
  unfold inferCanonicalParityBlock at hinfer
  unfold inferCanonicalParityBlock
  cases hfalse :
      inferCanonicalParityBlockWithCharge f false with
  | some bf =>
      simp [hfalse] at hinfer
      cases hinfer
      cases
        inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_supportVars_cons
          hperm hfvars hgvars hf hg hfalse with
      | intro bg hrest =>
          cases hrest with
          | intro hbg hrest2 =>
              cases hrest2 with
              | intro hspec hblock =>
                  exact Exists.intro bg
                    (And.intro (by simp [hbg])
                      (And.intro hspec hblock))
  | none =>
      simp [hfalse] at hinfer
      have hfalseG :
          inferCanonicalParityBlockWithCharge g false = none :=
        inferCanonicalParityBlockWithCharge_eq_none_of_perm_of_inferredSpec_eq
          hperm
          ((inferredCanonicalParityBlockSpec_eq_of_supportVars_cons
            hfvars hgvars hf hg false).symm)
          hfalse
      cases
        inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_supportVars_cons
          hperm hfvars hgvars hf hg hinfer with
      | intro bg hrest =>
          cases hrest with
          | intro hbg hrest2 =>
              cases hrest2 with
              | intro hspec hblock =>
                  exact Exists.intro bg
                    (And.intro (by simp [hfalseG, hbg])
                      (And.intro hspec hblock))

/--
For a nonempty executable support group, fixed-charge recognizer hits transport
across clause permutations without requiring callers to provide the
support-homogeneity proof separately.
-/
theorem inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons
    {m : Nat}
    {source : CNFModel.CNF m}
    {group : CanonicalSupportClauseGroup m}
    {target : CNFModel.CNF m}
    {cf cg : CNFModel.Clause m}
    {ftail gtail : CNFModel.CNF m}
    {charge : Bool}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    (hgroup : List.Mem group (groupClausesByCanonicalSupport source))
    (hperm : List.Perm target group.2)
    (hsource : group.2 = cf :: ftail)
    (htarget : target = cg :: gtail)
    (hinfer : inferCanonicalParityBlockWithCharge group.2 charge = some b) :
    exists b' : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlockWithCharge target charge = some b' /\
        b'.spec = b.spec /\
          List.Perm b'.blockCNF b.blockCNF := by
  have hsourceVars :
      CNFClausesHaveCanonicalSupportVars
        group.2 (canonicalClauseSupportVars cf) :=
    supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons
      hgroup hsource
  have htargetVars :
      CNFClausesHaveCanonicalSupportVars
        target (canonicalClauseSupportVars cf) :=
    cnfClausesHaveCanonicalSupportVars_of_perm hperm hsourceVars
  exact
    inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_supportVars_cons
      hperm hsourceVars htargetVars hsource htarget hinfer

/--
For a nonempty executable support group, public recognizer hits transport
across clause permutations without requiring callers to provide the
support-homogeneity proof separately.
-/
theorem inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons
    {m : Nat}
    {source : CNFModel.CNF m}
    {group : CanonicalSupportClauseGroup m}
    {target : CNFModel.CNF m}
    {cf cg : CNFModel.Clause m}
    {ftail gtail : CNFModel.CNF m}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    (hgroup : List.Mem group (groupClausesByCanonicalSupport source))
    (hperm : List.Perm target group.2)
    (hsource : group.2 = cf :: ftail)
    (htarget : target = cg :: gtail)
    (hinfer : inferCanonicalParityBlock group.2 = some b) :
    exists b' : CanonicalFingerprintRecognizedParityBlock m,
      inferCanonicalParityBlock target = some b' /\
        b'.spec = b.spec /\
          List.Perm b'.blockCNF b.blockCNF := by
  have hsourceVars :
      CNFClausesHaveCanonicalSupportVars
        group.2 (canonicalClauseSupportVars cf) :=
    supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons
      hgroup hsource
  have htargetVars :
      CNFClausesHaveCanonicalSupportVars
        target (canonicalClauseSupportVars cf) :=
    cnfClausesHaveCanonicalSupportVars_of_perm hperm hsourceVars
  exact
    inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons
      hperm hsourceVars htargetVars hsource htarget hinfer

/--
Every source group in a list came from the executable grouper for `source`.
This lets list-level transport theorems retain the group-level support
homogeneity established for actual grouped components.
-/
def SupportGroupsFromGrouper {m : Nat}
    (source : CNFModel.CNF m)
    (groups : List (CanonicalSupportClauseGroup m)) : Prop :=
  forall g : CanonicalSupportClauseGroup m,
    List.Mem g groups -> List.Mem g (groupClausesByCanonicalSupport source)

/-- The executable grouper's own output is, trivially, from that grouper. -/
theorem supportGroupsFromGrouper_self
    {m : Nat}
    (source : CNFModel.CNF m) :
    SupportGroupsFromGrouper source (groupClausesByCanonicalSupport source) := by
  intro g hg
  exact hg

/--
An aligned component-wise permutation relation for support-group lists.  Each
pair of groups carries a clause-list permutation and nonempty witnesses for the
source and target group CNFs.
-/
def AlignedSupportGroupCNFPermNonempty {m : Nat} :
    List (CanonicalSupportClauseGroup m) ->
      List (CanonicalSupportClauseGroup m) -> Prop
  | [], [] => True
  | sourceGroup :: sourceGroups, targetGroup :: targetGroups =>
      (exists sourceHead : CNFModel.Clause m,
        exists sourceTail : CNFModel.CNF m,
          exists targetHead : CNFModel.Clause m,
            exists targetTail : CNFModel.CNF m,
              List.Perm targetGroup.2 sourceGroup.2 /\
                sourceGroup.2 = sourceHead :: sourceTail /\
                  targetGroup.2 = targetHead :: targetTail) /\
        AlignedSupportGroupCNFPermNonempty sourceGroups targetGroups
  | _, _ => False

/--
A transported canonical block has the same inferred parity spec and a
clause-permuted stored block CNF.
-/
def RecognizedBlockTransport {m : Nat}
    (target source : CanonicalFingerprintRecognizedParityBlock m) : Prop :=
  target.spec = source.spec /\ List.Perm target.blockCNF source.blockCNF

/-- Aligned block-list transport for canonical splitter outputs. -/
def RecognizedBlocksTransport {m : Nat} :
    List (CanonicalFingerprintRecognizedParityBlock m) ->
      List (CanonicalFingerprintRecognizedParityBlock m) -> Prop
  | [], [] => True
  | target :: targets, source :: sources =>
      RecognizedBlockTransport target source /\
        RecognizedBlocksTransport targets sources
  | _, _ => False

/-- Equal transported specs imply equal compact GF(2) equations. -/
theorem recognizedBlockTransport_compactGF2_eq
    {m : Nat}
    {target source : CanonicalFingerprintRecognizedParityBlock m}
    (htransport : RecognizedBlockTransport target source) :
    target.compactGF2 = source.compactGF2 := by
  unfold RecognizedBlockTransport at htransport
  unfold CanonicalFingerprintRecognizedParityBlock.compactGF2
  rw [htransport.1]

/-- Transported block lists have identical compact GF(2) output. -/
theorem canonicalFingerprintRecognizedBlocksGF2_eq_of_recognizedBlocksTransport
    {m : Nat}
    {target source : List (CanonicalFingerprintRecognizedParityBlock m)}
    (htransport : RecognizedBlocksTransport target source) :
    canonicalFingerprintRecognizedBlocksGF2 target =
      canonicalFingerprintRecognizedBlocksGF2 source := by
  induction target generalizing source with
  | nil =>
      cases source with
      | nil =>
          rfl
      | cons _ _ =>
          cases htransport
  | cons targetBlock targetBlocks ih =>
      cases source with
      | nil =>
          cases htransport
      | cons sourceBlock sourceBlocks =>
          have hhead :
              RecognizedBlockTransport targetBlock sourceBlock :=
            htransport.1
          have htail :
              RecognizedBlocksTransport targetBlocks sourceBlocks :=
            htransport.2
          have hcompact :
              targetBlock.compactGF2 = sourceBlock.compactGF2 :=
            recognizedBlockTransport_compactGF2_eq hhead
          change
            targetBlock.compactGF2 ::
                canonicalFingerprintRecognizedBlocksGF2 targetBlocks =
              sourceBlock.compactGF2 ::
                canonicalFingerprintRecognizedBlocksGF2 sourceBlocks
          rw [hcompact, ih htail]

/--
Recognition evidence transports across aligned nonempty support-group
permutations.  The target blocks may store permuted CNFs, so the conclusion is
phrased with `RecognizedBlocksTransport` instead of exact block-list equality.
-/
theorem groupsRecognized_transport_of_alignedGroupCNFPerm
    {m : Nat}
    {source : CNFModel.CNF m}
    {sourceGroups targetGroups : List (CanonicalSupportClauseGroup m)}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hfrom : SupportGroupsFromGrouper source sourceGroups)
    (haligned :
      AlignedSupportGroupCNFPermNonempty sourceGroups targetGroups)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized sourceGroups sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized targetGroups targetBlocks /\
        RecognizedBlocksTransport targetBlocks sourceBlocks := by
  induction sourceGroups generalizing targetGroups sourceBlocks with
  | nil =>
      cases targetGroups with
      | nil =>
          cases sourceBlocks with
          | nil =>
              exact Exists.intro [] (And.intro True.intro True.intro)
          | cons _ _ =>
              cases hrecognized
      | cons _ _ =>
          cases haligned
  | cons sourceGroup sourceGroups ih =>
      cases targetGroups with
      | nil =>
          cases haligned
      | cons targetGroup targetGroups =>
          have hpair := haligned.1
          have htailAligned :
              AlignedSupportGroupCNFPermNonempty sourceGroups targetGroups :=
            haligned.2
          cases sourceBlocks with
          | nil =>
              cases hrecognized
          | cons sourceBlock sourceBlocks =>
              have hheadRecognized :
                  inferCanonicalParityBlock sourceGroup.2 = some sourceBlock :=
                hrecognized.1
              have htailRecognized :
                  ExtractorCompleteness.GroupsRecognized sourceGroups sourceBlocks :=
                hrecognized.2
              have hgroup :
                  List.Mem sourceGroup (groupClausesByCanonicalSupport source) :=
                hfrom sourceGroup (List.Mem.head sourceGroups)
              cases hpair with
              | intro sourceHead hpair =>
                  cases hpair with
                  | intro sourceTail hpair =>
                      cases hpair with
                      | intro targetHead hpair =>
                          cases hpair with
                          | intro targetTail hpair =>
                              have hperm : List.Perm targetGroup.2 sourceGroup.2 :=
                                hpair.1
                              have hsource :
                                  sourceGroup.2 = sourceHead :: sourceTail :=
                                hpair.2.1
                              have htarget :
                                  targetGroup.2 = targetHead :: targetTail :=
                                hpair.2.2
                              cases
                                inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons
                                  hgroup hperm hsource htarget hheadRecognized with
                              | intro targetBlock htransportHead =>
                                  have htargetRecognized :
                                      inferCanonicalParityBlock targetGroup.2 =
                                        some targetBlock :=
                                    htransportHead.1
                                  have hspec : targetBlock.spec = sourceBlock.spec :=
                                    htransportHead.2.1
                                  have hblockPerm :
                                      List.Perm targetBlock.blockCNF
                                        sourceBlock.blockCNF :=
                                    htransportHead.2.2
                                  have hfromTail :
                                      SupportGroupsFromGrouper source sourceGroups := by
                                    intro g hg
                                    exact hfrom g (List.Mem.tail sourceGroup hg)
                                  cases
                                    ih hfromTail htailAligned htailRecognized with
                                  | intro targetBlocks htailResult =>
                                      exact
                                        Exists.intro (targetBlock :: targetBlocks)
                                          (And.intro
                                            (And.intro htargetRecognized
                                              htailResult.1)
                                            (And.intro
                                              (And.intro hspec hblockPerm)
                                              htailResult.2))

/--
Residual-free splitter output transports across aligned nonempty support-group
permutations, preserving compact GF(2) output exactly and block CNFs up to
per-component permutation.
-/
theorem splitCanonicalSupportClauseGroups_transport_of_alignedGroupCNFPerm
    {m : Nat}
    {source : CNFModel.CNF m}
    {sourceGroups targetGroups : List (CanonicalSupportClauseGroup m)}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hfrom : SupportGroupsFromGrouper source sourceGroups)
    (haligned :
      AlignedSupportGroupCNFPermNonempty sourceGroups targetGroups)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized sourceGroups sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      splitCanonicalSupportClauseGroups targetGroups =
        { blocks := targetBlocks, residualCNF := [] } /\
        RecognizedBlocksTransport targetBlocks sourceBlocks /\
          canonicalFingerprintRecognizedBlocksGF2 targetBlocks =
            canonicalFingerprintRecognizedBlocksGF2 sourceBlocks := by
  cases
    groupsRecognized_transport_of_alignedGroupCNFPerm
      hfrom haligned hrecognized with
  | intro targetBlocks htransportResult =>
      exact
        Exists.intro targetBlocks
          (And.intro
            (ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
              htransportResult.1)
            (And.intro htransportResult.2
              (canonicalFingerprintRecognizedBlocksGF2_eq_of_recognizedBlocksTransport
                htransportResult.2)))

/--
Recognition evidence transports across support-group list permutations.  This
is the group-order half of whole-CNF interleaving: if the same recognized
components are emitted in a different order, the splitter can emit a
correspondingly permuted block list and the compact GF(2) output is preserved up
to `List.Perm`.
-/
theorem groupsRecognized_transport_of_group_perm
    {m : Nat}
    {targetGroups sourceGroups : List (CanonicalSupportClauseGroup m)}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm targetGroups sourceGroups)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized sourceGroups sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized targetGroups targetBlocks /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 targetBlocks)
          (canonicalFingerprintRecognizedBlocksGF2 sourceBlocks) := by
  induction hperm generalizing sourceBlocks with
  | nil =>
      cases sourceBlocks with
      | nil =>
          exact Exists.intro [] (And.intro True.intro (List.Perm.refl []))
      | cons _ _ =>
          cases hrecognized
  | cons group _htail ih =>
      cases sourceBlocks with
      | nil =>
          cases hrecognized
      | cons sourceBlock sourceBlocks =>
          have hhead :
              inferCanonicalParityBlock group.2 = some sourceBlock :=
            hrecognized.1
          have htailRecognized :
              ExtractorCompleteness.GroupsRecognized _ sourceBlocks :=
            hrecognized.2
          cases ih htailRecognized with
          | intro targetBlocks htarget =>
              have hgf2 :
                  List.Perm
                    (canonicalFingerprintRecognizedBlocksGF2
                      (sourceBlock :: targetBlocks))
                    (canonicalFingerprintRecognizedBlocksGF2
                      (sourceBlock :: sourceBlocks)) := by
                simpa [canonicalFingerprintRecognizedBlocksGF2] using
                  List.Perm.cons sourceBlock.compactGF2 htarget.2
              exact
                Exists.intro (sourceBlock :: targetBlocks)
                  (And.intro (And.intro hhead htarget.1) hgf2)
  | swap leftGroup rightGroup groups =>
      cases sourceBlocks with
      | nil =>
          cases hrecognized
      | cons leftBlock sourceBlocks =>
          cases sourceBlocks with
          | nil =>
              cases hrecognized.2
          | cons rightBlock tailBlocks =>
              have hleft :
                  inferCanonicalParityBlock leftGroup.2 = some leftBlock :=
                hrecognized.1
              have hright :
                  inferCanonicalParityBlock rightGroup.2 = some rightBlock :=
                hrecognized.2.1
              have htail :
                  ExtractorCompleteness.GroupsRecognized groups tailBlocks :=
                hrecognized.2.2
              have hgf2 :
                  List.Perm
                    (canonicalFingerprintRecognizedBlocksGF2
                      (rightBlock :: leftBlock :: tailBlocks))
                    (canonicalFingerprintRecognizedBlocksGF2
                      (leftBlock :: rightBlock :: tailBlocks)) := by
                simpa [canonicalFingerprintRecognizedBlocksGF2] using
                  (List.Perm.swap leftBlock.compactGF2
                    rightBlock.compactGF2
                    (canonicalFingerprintRecognizedBlocksGF2 tailBlocks))
              exact
                Exists.intro (rightBlock :: leftBlock :: tailBlocks)
                  (And.intro
                    (And.intro hright (And.intro hleft htail))
                    hgf2)
  | trans _hleft _hright ihleft ihright =>
      cases ihright hrecognized with
      | intro midBlocks hmid =>
          cases ihleft hmid.1 with
          | intro targetBlocks htarget =>
              exact
                Exists.intro targetBlocks
                  (And.intro htarget.1
                    (List.Perm.trans htarget.2 hmid.2))

/--
Residual-free splitter output transports across support-group list
permutations, preserving the compact GF(2) output up to `List.Perm`.
-/
theorem splitCanonicalSupportClauseGroups_transport_of_group_perm
    {m : Nat}
    {targetGroups sourceGroups : List (CanonicalSupportClauseGroup m)}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm targetGroups sourceGroups)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized sourceGroups sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      splitCanonicalSupportClauseGroups targetGroups =
        { blocks := targetBlocks, residualCNF := [] } /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 targetBlocks)
          (canonicalFingerprintRecognizedBlocksGF2 sourceBlocks) := by
  cases groupsRecognized_transport_of_group_perm hperm hrecognized with
  | intro targetBlocks htarget =>
      exact
        Exists.intro targetBlocks
          (And.intro
            (ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
              htarget.1)
            htarget.2)

/--
Inserting one clause into canonical support groups preserves the covered CNF up
to permutation, adding exactly that clause.
-/
theorem canonicalSupportClauseGroupsCNF_insertClauseByCanonicalSupport_perm
    {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m)) :
    List.Perm
      (ExtractorCompleteness.canonicalSupportClauseGroupsCNF
        (insertClauseByCanonicalSupport c groups))
      (ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups ++ [c]) := by
  induction groups with
  | nil =>
      simp [insertClauseByCanonicalSupport,
        ExtractorCompleteness.canonicalSupportClauseGroupsCNF]
  | cons g groups ih =>
      by_cases hkey : canonicalClauseSupportKey c = g.1
      case pos =>
        have hswap :
            List.Perm
              ((g.2 ++ [c]) ++
                ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups)
              ((g.2 ++
                ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups) ++
                  [c]) := by
          simpa [List.append_assoc] using
            List.Perm.append_left g.2
              (List.perm_append_comm :
                List.Perm
                  ([c] ++
                    ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups)
                  (ExtractorCompleteness.canonicalSupportClauseGroupsCNF
                    groups ++ [c]))
        simpa [insertClauseByCanonicalSupport, hkey,
          ExtractorCompleteness.canonicalSupportClauseGroupsCNF,
          List.append_assoc] using hswap
      case neg =>
        have hrest :
            List.Perm
              (g.2 ++
                ExtractorCompleteness.canonicalSupportClauseGroupsCNF
                  (insertClauseByCanonicalSupport c groups))
              (g.2 ++
                (ExtractorCompleteness.canonicalSupportClauseGroupsCNF
                  groups ++ [c])) :=
          List.Perm.append_left g.2 ih
        simpa [insertClauseByCanonicalSupport, hkey,
          ExtractorCompleteness.canonicalSupportClauseGroupsCNF,
          List.append_assoc] using hrest

/-- Folding a CNF into canonical support groups preserves covered clauses. -/
theorem canonicalSupportClauseGroupsCNF_fold_insert_perm
    {m : Nat}
    (f : CNFModel.CNF m)
    (groups : List (CanonicalSupportClauseGroup m)) :
    List.Perm
      (ExtractorCompleteness.canonicalSupportClauseGroupsCNF
        (f.foldl
          (fun groups c => insertClauseByCanonicalSupport c groups)
          groups))
      (ExtractorCompleteness.canonicalSupportClauseGroupsCNF groups ++ f) := by
  induction f generalizing groups with
  | nil =>
      simp
  | cons c f ih =>
      have hih :=
        ih (insertClauseByCanonicalSupport c groups)
      have hins :=
        canonicalSupportClauseGroupsCNF_insertClauseByCanonicalSupport_perm
          c groups
      exact
        List.Perm.trans hih
          (by
            simpa [List.append_assoc] using
              List.Perm.append_right f hins)

/-- Canonical support grouping preserves the input CNF clauses up to permutation. -/
theorem canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm
    {m : Nat}
    (f : CNFModel.CNF m) :
    List.Perm
      (ExtractorCompleteness.canonicalSupportClauseGroupsCNF
        (groupClausesByCanonicalSupport f))
      f := by
  unfold groupClausesByCanonicalSupport
  simpa [ExtractorCompleteness.canonicalSupportClauseGroupsCNF] using
    canonicalSupportClauseGroupsCNF_fold_insert_perm f
      ([] : List (CanonicalSupportClauseGroup m))

/--
Every key in the result of inserting one clause either was already present in
the old group list or is the inserted clause's key.
-/
theorem mem_groupKeys_insertClauseByCanonicalSupport
    {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m))
    {key : CanonicalClauseSupportKey}
    (hmem :
      List.Mem key
        (groupKeys (insertClauseByCanonicalSupport c groups))) :
    key = canonicalClauseSupportKey c \/ List.Mem key (groupKeys groups) := by
  induction groups with
  | nil =>
      change List.Mem key [canonicalClauseSupportKey c] at hmem
      cases hmem with
      | head =>
          exact Or.inl rfl
      | tail _ htail =>
          cases htail
  | cons g groups ih =>
      by_cases hkey : canonicalClauseSupportKey c = g.1
      case pos =>
        have hold :
            List.Mem key (groupKeys (g :: groups)) := by
          simpa [insertClauseByCanonicalSupport, hkey, groupKeys]
            using hmem
        exact Or.inr hold
      case neg =>
        have hsplit :
            List.Mem key
              (g.1 ::
                groupKeys
                  (insertClauseByCanonicalSupport c groups)) := by
          simpa [insertClauseByCanonicalSupport, hkey, groupKeys]
            using hmem
        cases hsplit with
        | head =>
            exact
              Or.inr
                (by
                  unfold groupKeys
                  exact List.Mem.head (List.map Prod.fst groups))
        | tail _ htail =>
            exact
              match ih htail with
              | Or.inl hnew => Or.inl hnew
              | Or.inr hold =>
                  Or.inr
                    (by
                      unfold groupKeys at hold
                      unfold groupKeys
                      exact List.Mem.tail g.1 hold)

/--
After folding a CNF into an existing support-group accumulator, every output
key either came from the accumulator or from one of the folded clauses.
-/
theorem mem_groupKeys_fold_insert
    {m : Nat}
    (f : CNFModel.CNF m)
    (groups : List (CanonicalSupportClauseGroup m))
    {key : CanonicalClauseSupportKey}
    (hmem :
      List.Mem key
        (groupKeys
          (f.foldl
            (fun groups c => insertClauseByCanonicalSupport c groups)
            groups))) :
    List.Mem key (groupKeys groups) \/
      exists c : CNFModel.Clause m,
        List.Mem c f /\ key = canonicalClauseSupportKey c := by
  induction f generalizing groups with
  | nil =>
      exact Or.inl hmem
  | cons c f ih =>
      have hstep :=
        ih (insertClauseByCanonicalSupport c groups) hmem
      cases hstep with
      | inl hacc =>
          exact
            match mem_groupKeys_insertClauseByCanonicalSupport
              c groups hacc with
            | Or.inl hnew =>
                Or.inr
                  (Exists.intro c
                    (And.intro (List.Mem.head f) hnew))
            | Or.inr hold =>
                Or.inl hold
      | inr hfromTail =>
          cases hfromTail with
          | intro d hdAnd =>
              cases hdAnd with
              | intro hd hkey =>
                  exact
                    Or.inr
                      (Exists.intro d
                        (And.intro (List.Mem.tail c hd) hkey))

/-- Every grouped canonical support key came from some input clause. -/
theorem mem_groupKeys_groupClausesByCanonicalSupport
    {m : Nat}
    (f : CNFModel.CNF m)
    {key : CanonicalClauseSupportKey}
    (hmem :
      List.Mem key (groupKeys (groupClausesByCanonicalSupport f))) :
    exists c : CNFModel.Clause m,
      List.Mem c f /\ key = canonicalClauseSupportKey c := by
  have hfold :=
    mem_groupKeys_fold_insert f
      ([] : List (CanonicalSupportClauseGroup m))
      (key := key)
  unfold groupClausesByCanonicalSupport at hmem
  have hresult := hfold hmem
  cases hresult with
  | inl hnil =>
      cases hnil
      | inr hfrom =>
          exact hfrom

/-- Inserting one clause preserves every old canonical support key. -/
theorem mem_groupKeys_insertClauseByCanonicalSupport_of_mem
    {m : Nat}
    (c : CNFModel.Clause m)
    {groups : List (CanonicalSupportClauseGroup m)}
    {key : CanonicalClauseSupportKey}
    (hmem : List.Mem key (groupKeys groups)) :
    List.Mem key
      (groupKeys (insertClauseByCanonicalSupport c groups)) := by
  induction groups with
  | nil =>
      cases hmem
  | cons g groups ih =>
      by_cases hkey : canonicalClauseSupportKey c = g.1
      case pos =>
        simpa [insertClauseByCanonicalSupport, hkey, groupKeys] using hmem
      case neg =>
        have hresult :
            List.Mem key
              (g.1 ::
                groupKeys (insertClauseByCanonicalSupport c groups)) := by
          cases hmem with
          | head =>
              exact List.Mem.head _
          | tail _ htail =>
              exact List.Mem.tail g.1 (ih htail)
        simpa [insertClauseByCanonicalSupport, hkey, groupKeys]
          using hresult

/-- Inserting one clause adds that clause's canonical support key. -/
theorem mem_groupKeys_insertClauseByCanonicalSupport_self
    {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m)) :
    List.Mem (canonicalClauseSupportKey c)
      (groupKeys (insertClauseByCanonicalSupport c groups)) := by
  induction groups with
  | nil =>
      change List.Mem (canonicalClauseSupportKey c)
        [canonicalClauseSupportKey c]
      exact List.Mem.head []
  | cons g groups ih =>
      by_cases hkey : canonicalClauseSupportKey c = g.1
      case pos =>
        have hresult :
            List.Mem (canonicalClauseSupportKey c)
              (g.1 :: groupKeys groups) := by
          simpa [hkey] using
            (List.Mem.head (groupKeys groups) :
              List.Mem g.1 (g.1 :: groupKeys groups))
        simpa [insertClauseByCanonicalSupport, hkey, groupKeys]
          using hresult
      case neg =>
        have hresult :
            List.Mem (canonicalClauseSupportKey c)
              (g.1 ::
                groupKeys (insertClauseByCanonicalSupport c groups)) :=
          List.Mem.tail g.1 ih
        simpa [insertClauseByCanonicalSupport, hkey, groupKeys]
          using hresult

/-- Folding more clauses into support groups preserves every old key. -/
theorem mem_groupKeys_fold_insert_of_mem_groupKey
    {m : Nat}
    (f : CNFModel.CNF m)
    {groups : List (CanonicalSupportClauseGroup m)}
    {key : CanonicalClauseSupportKey}
    (hmem : List.Mem key (groupKeys groups)) :
    List.Mem key
      (groupKeys
        (f.foldl
          (fun groups c => insertClauseByCanonicalSupport c groups)
          groups)) := by
  induction f generalizing groups with
  | nil =>
      exact hmem
  | cons c _ ih =>
      exact ih
        (mem_groupKeys_insertClauseByCanonicalSupport_of_mem c hmem)

/-- Folding a CNF into support groups records every folded clause's key. -/
theorem mem_groupKeys_fold_insert_of_mem_clause
    {m : Nat}
    (f : CNFModel.CNF m)
    (groups : List (CanonicalSupportClauseGroup m))
    {c : CNFModel.Clause m}
    (hc : List.Mem c f) :
    List.Mem (canonicalClauseSupportKey c)
      (groupKeys
        (f.foldl
          (fun groups c => insertClauseByCanonicalSupport c groups)
          groups)) := by
  induction f generalizing groups with
  | nil =>
      cases hc
  | cons d f ih =>
      cases hc with
      | head =>
          exact mem_groupKeys_fold_insert_of_mem_groupKey f
            (mem_groupKeys_insertClauseByCanonicalSupport_self c groups)
      | tail _ htail =>
          exact ih (insertClauseByCanonicalSupport d groups) htail

/-- Every input clause contributes its canonical support key to the grouped key list. -/
theorem mem_groupKeys_groupClausesByCanonicalSupport_of_mem
    {m : Nat}
    {f : CNFModel.CNF m}
    {c : CNFModel.Clause m}
    (hc : List.Mem c f) :
    List.Mem (canonicalClauseSupportKey c)
      (groupKeys (groupClausesByCanonicalSupport f)) := by
  unfold groupClausesByCanonicalSupport
  exact mem_groupKeys_fold_insert_of_mem_clause f
    ([] : List (CanonicalSupportClauseGroup m)) hc

/--
Grouped canonical support keys are exactly the canonical support keys of input
clauses.
-/
theorem mem_groupKeys_groupClausesByCanonicalSupport_iff
    {m : Nat}
    (f : CNFModel.CNF m)
    {key : CanonicalClauseSupportKey} :
    List.Mem key (groupKeys (groupClausesByCanonicalSupport f)) <->
      exists c : CNFModel.Clause m,
        List.Mem c f /\ key = canonicalClauseSupportKey c := by
  constructor
  case mp =>
      exact mem_groupKeys_groupClausesByCanonicalSupport f
  case mpr =>
      intro h
      rcases h with ⟨c, hc, hkey⟩
      rw [hkey]
      exact mem_groupKeys_groupClausesByCanonicalSupport_of_mem hc

/-- Inserting one clause preserves the no-duplicate invariant on group keys. -/
theorem nodup_groupKeys_insertClauseByCanonicalSupport
    {m : Nat}
    (c : CNFModel.Clause m)
    {groups : List (CanonicalSupportClauseGroup m)}
    (hnodup : (groupKeys groups).Nodup) :
    (groupKeys (insertClauseByCanonicalSupport c groups)).Nodup := by
  induction groups with
  | nil =>
      simp [insertClauseByCanonicalSupport, groupKeys]
  | cons g groups ih =>
      by_cases hkey : canonicalClauseSupportKey c = g.1
      case pos =>
        simpa [insertClauseByCanonicalSupport, hkey, groupKeys] using hnodup
      case neg =>
        have hnodupCons :
            (g.1 :: groupKeys groups).Nodup := by
          simpa [groupKeys] using hnodup
        have hnot :
            Not
              (List.Mem g.1
                (groupKeys (insertClauseByCanonicalSupport c groups))) := by
          intro hmem
          have hsplit :=
            mem_groupKeys_insertClauseByCanonicalSupport c groups hmem
          cases hsplit with
          | inl hnew =>
              exact hkey hnew.symm
          | inr hold =>
              exact (List.nodup_cons.mp hnodupCons).1 hold
        have htail :
            (groupKeys (insertClauseByCanonicalSupport c groups)).Nodup :=
          ih (List.nodup_cons.mp hnodupCons).2
        have hresult :
            (g.1 ::
              groupKeys (insertClauseByCanonicalSupport c groups)).Nodup :=
          List.nodup_cons.mpr (And.intro hnot htail)
        simpa [insertClauseByCanonicalSupport, hkey, groupKeys]
          using hresult

/-- Folding clauses into support groups preserves the no-duplicate key invariant. -/
theorem nodup_groupKeys_fold_insert
    {m : Nat}
    (f : CNFModel.CNF m)
    {groups : List (CanonicalSupportClauseGroup m)}
    (hnodup : (groupKeys groups).Nodup) :
    (groupKeys
      (f.foldl
        (fun groups c => insertClauseByCanonicalSupport c groups)
        groups)).Nodup := by
  induction f generalizing groups with
  | nil =>
      exact hnodup
  | cons c _ ih =>
      exact ih
        (nodup_groupKeys_insertClauseByCanonicalSupport c hnodup)

/-- The executable support grouper emits each canonical support key at most once. -/
theorem nodup_groupKeys_groupClausesByCanonicalSupport
    {m : Nat}
    (f : CNFModel.CNF m) :
    (groupKeys (groupClausesByCanonicalSupport f)).Nodup := by
  unfold groupClausesByCanonicalSupport
  exact nodup_groupKeys_fold_insert f
    (groups := ([] : List (CanonicalSupportClauseGroup m)))
    (by simp [groupKeys])

/--
Arbitrary CNF permutation preserves the grouped canonical support-key list up
to permutation.  This is the key-set layer needed before proving whole-CNF
interleaving invariance for recognized components.
-/
theorem groupKeys_groupClausesByCanonicalSupport_perm_of_perm
    {m : Nat}
    {f g : CNFModel.CNF m}
    (hperm : List.Perm f g) :
    List.Perm
      (groupKeys (groupClausesByCanonicalSupport f))
      (groupKeys (groupClausesByCanonicalSupport g)) := by
  apply List.perm_iff_count.2
  intro key
  rw [List.count_eq_of_nodup
        (nodup_groupKeys_groupClausesByCanonicalSupport f),
      List.count_eq_of_nodup
        (nodup_groupKeys_groupClausesByCanonicalSupport g)]
  by_cases hfmem :
      key ∈ groupKeys (groupClausesByCanonicalSupport f)
  case pos =>
      have hgmem :
          key ∈ groupKeys (groupClausesByCanonicalSupport g) := by
        rcases
          (mem_groupKeys_groupClausesByCanonicalSupport_iff f).1 hfmem with
          ⟨c, hcf, hkey⟩
        exact
          (mem_groupKeys_groupClausesByCanonicalSupport_iff g).2
            ⟨c, hperm.subset hcf, hkey⟩
      rw [if_pos hfmem, if_pos hgmem]
  case neg =>
      have hgmem :
          Not (key ∈ groupKeys (groupClausesByCanonicalSupport g)) := by
        intro hmem
        rcases
          (mem_groupKeys_groupClausesByCanonicalSupport_iff g).1 hmem with
          ⟨c, hcg, hkey⟩
        exact hfmem
          ((mem_groupKeys_groupClausesByCanonicalSupport_iff f).2
            ⟨c, hperm.symm.subset hcg, hkey⟩)
      rw [if_neg hfmem, if_neg hgmem]

/--
Inserting one clause preserves the selected-key group content up to
permutation, adding exactly the inserted clause when its key matches.
-/
theorem groupClausesForKey_insertClauseByCanonicalSupport_perm
    {m : Nat}
    (key : CanonicalClauseSupportKey)
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m)) :
    List.Perm
      (groupClausesForKey key (insertClauseByCanonicalSupport c groups))
      (groupClausesForKey key groups ++ cnfClausesForKey key [c]) := by
  induction groups with
  | nil =>
      by_cases hckey : canonicalClauseSupportKey c = key
      · simp [insertClauseByCanonicalSupport, groupClausesForKey,
          cnfClausesForKey, hckey]
      · simp [insertClauseByCanonicalSupport, groupClausesForKey,
          cnfClausesForKey, hckey]
  | cons g groups ih =>
      by_cases hinsert : canonicalClauseSupportKey c = g.1
      · by_cases hgroup : g.1 = key
        · have hcKey : canonicalClauseSupportKey c = key := by
            rw [hinsert, hgroup]
          have hswap :
              List.Perm
                ((g.2 ++ [c]) ++ groupClausesForKey key groups)
                ((g.2 ++ groupClausesForKey key groups) ++ [c]) := by
            simpa [List.append_assoc] using
              List.Perm.append_left g.2
                (List.perm_append_comm :
                  List.Perm
                    ([c] ++ groupClausesForKey key groups)
                    (groupClausesForKey key groups ++ [c]))
          simpa [insertClauseByCanonicalSupport, hinsert,
            groupClausesForKey, cnfClausesForKey, hgroup, hcKey,
            List.append_assoc] using hswap
        · have hcNotKey : Not (canonicalClauseSupportKey c = key) := by
            intro hcKey
            exact hgroup (hinsert.symm.trans hcKey)
          simp [insertClauseByCanonicalSupport, hinsert,
            groupClausesForKey, cnfClausesForKey, hgroup, hcNotKey]
      · by_cases hgroup : g.1 = key
        · have htail :
              List.Perm
                (g.2 ++
                  groupClausesForKey key
                    (insertClauseByCanonicalSupport c groups))
                (g.2 ++
                  (groupClausesForKey key groups ++
                    cnfClausesForKey key [c])) :=
            List.Perm.append_left g.2 ih
          have hcNotKey : Not (canonicalClauseSupportKey c = key) := by
            intro hcKey
            exact hinsert (hcKey.trans hgroup.symm)
          simpa [insertClauseByCanonicalSupport, hinsert,
            groupClausesForKey, hgroup, hcNotKey, List.append_assoc] using htail
        · simpa [insertClauseByCanonicalSupport, hinsert,
            groupClausesForKey, hgroup] using ih

/--
Folding a CNF into support groups preserves the selected-key group content up
to permutation.
-/
theorem groupClausesForKey_fold_insert_perm
    {m : Nat}
    (key : CanonicalClauseSupportKey)
    (f : CNFModel.CNF m)
    (groups : List (CanonicalSupportClauseGroup m)) :
    List.Perm
      (groupClausesForKey key
        (f.foldl
          (fun groups c => insertClauseByCanonicalSupport c groups)
          groups))
      (groupClausesForKey key groups ++ cnfClausesForKey key f) := by
  induction f generalizing groups with
  | nil =>
      simp [cnfClausesForKey]
  | cons c f ih =>
      have hih :=
        ih (insertClauseByCanonicalSupport c groups)
      have hins :=
        groupClausesForKey_insertClauseByCanonicalSupport_perm key c groups
      have happ :
          List.Perm
            (groupClausesForKey key
                (insertClauseByCanonicalSupport c groups) ++
              cnfClausesForKey key f)
            ((groupClausesForKey key groups ++
                cnfClausesForKey key [c]) ++
              cnfClausesForKey key f) :=
        List.Perm.append_right (cnfClausesForKey key f) hins
      have hfilter :
          cnfClausesForKey key (c :: f) =
            cnfClausesForKey key [c] ++ cnfClausesForKey key f := by
        by_cases hckey : canonicalClauseSupportKey c = key
        · simp [cnfClausesForKey, hckey]
        · simp [cnfClausesForKey, hckey]
      exact
        List.Perm.trans hih
          (by
            rw [hfilter]
            simpa [List.append_assoc] using happ)

/--
For any canonical support key, the executable support groups contain exactly
the input clauses with that key, up to permutation.
-/
theorem groupClausesForKey_groupClausesByCanonicalSupport_perm
    {m : Nat}
    (key : CanonicalClauseSupportKey)
    (f : CNFModel.CNF m) :
    List.Perm
      (groupClausesForKey key (groupClausesByCanonicalSupport f))
      (cnfClausesForKey key f) := by
  unfold groupClausesByCanonicalSupport
  simpa [groupClausesForKey] using
    groupClausesForKey_fold_insert_perm key f
      ([] : List (CanonicalSupportClauseGroup m))

/--
Arbitrary CNF permutation preserves each canonical support key's grouped clause
content up to permutation.
-/
theorem groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm
    {m : Nat}
    (key : CanonicalClauseSupportKey)
    {f g : CNFModel.CNF m}
    (hperm : List.Perm f g) :
    List.Perm
      (groupClausesForKey key (groupClausesByCanonicalSupport f))
      (groupClausesForKey key (groupClausesByCanonicalSupport g)) := by
  exact
    List.Perm.trans
      (groupClausesForKey_groupClausesByCanonicalSupport_perm key f)
      (List.Perm.trans
        (hperm.filter
          (fun c => decide (canonicalClauseSupportKey c = key)))
        (groupClausesForKey_groupClausesByCanonicalSupport_perm key g).symm)

/-- If a key is absent from a support-group list, selecting that key is empty. -/
theorem groupClausesForKey_eq_nil_of_not_mem_groupKeys
    {m : Nat}
    {key : CanonicalClauseSupportKey}
    {groups : List (CanonicalSupportClauseGroup m)}
    (hnot : Not (List.Mem key (groupKeys groups))) :
    groupClausesForKey key groups = [] := by
  induction groups with
  | nil =>
      simp [groupClausesForKey]
  | cons group groups ih =>
      have hhead : Not (group.1 = key) := by
        intro hkey
        apply hnot
        have hmemHead :
            List.Mem group.1 (groupKeys (group :: groups)) := by
          unfold groupKeys
          exact List.Mem.head (List.map Prod.fst groups)
        simpa [hkey] using hmemHead
      have htail : Not (List.Mem key (groupKeys groups)) := by
        intro hmem
        apply hnot
        unfold groupKeys at hmem
        unfold groupKeys
        exact List.Mem.tail group.1 hmem
      simpa [groupClausesForKey, hhead] using ih htail

/--
With no duplicate group keys, selecting the key of a present group returns
that group's clause list up to permutation.
-/
theorem groupClausesForKey_perm_of_mem_group_nodup
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {group : CanonicalSupportClauseGroup m}
    (hnodup : (groupKeys groups).Nodup)
    (hmem : List.Mem group groups) :
    List.Perm (groupClausesForKey group.1 groups) group.2 := by
  induction groups with
  | nil =>
      cases hmem
  | cons first groups ih =>
      have hnodupCons :
          (first.1 :: groupKeys groups).Nodup := by
        simpa [groupKeys] using hnodup
      cases hmem with
      | head =>
          have hnotTail :
              Not (List.Mem group.1 (groupKeys groups)) :=
            (List.nodup_cons.mp hnodupCons).1
          have htailEmpty :
              groupClausesForKey group.1 groups = [] :=
            groupClausesForKey_eq_nil_of_not_mem_groupKeys hnotTail
          have hbindEmpty :
              (groups.filter (fun g => decide (g.1 = group.1))).bind
                  Prod.snd = [] := by
            simpa [groupClausesForKey] using htailEmpty
          simp [groupClausesForKey, hbindEmpty]
      | tail _ htailMem =>
          have htailNodup : (groupKeys groups).Nodup :=
            (List.nodup_cons.mp hnodupCons).2
          have hneq : Not (first.1 = group.1) := by
            intro hkey
            have hkeyMem :
                List.Mem group.1 (groupKeys groups) := by
              unfold groupKeys
              exact List.mem_map_of_mem Prod.fst htailMem
            exact (List.nodup_cons.mp hnodupCons).1
              (by
                rw [hkey]
                exact hkeyMem)
          simpa [groupClausesForKey, hneq] using
            ih htailNodup htailMem

/-- A key present in `groupKeys` is witnessed by a support group with that key. -/
theorem exists_group_of_mem_groupKeys
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {key : CanonicalClauseSupportKey}
    (hmem : List.Mem key (groupKeys groups)) :
    exists group : CanonicalSupportClauseGroup m,
      List.Mem group groups /\ group.1 = key := by
  unfold groupKeys at hmem
  exact List.mem_map.1 hmem

/--
Every source support group has a target support group with the same key and
permuted clause content.
-/
def SupportGroupsKeyMatchedCNFPerm {m : Nat}
    (source target : List (CanonicalSupportClauseGroup m)) : Prop :=
  forall sourceGroup : CanonicalSupportClauseGroup m,
    List.Mem sourceGroup source ->
      exists targetGroup : CanonicalSupportClauseGroup m,
        List.Mem targetGroup target /\
          targetGroup.1 = sourceGroup.1 /\
            List.Perm targetGroup.2 sourceGroup.2

/--
Arbitrary whole-CNF permutation induces key-matched component transport between
the executable support-group outputs.
-/
theorem supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm
    {m : Nat}
    {f g : CNFModel.CNF m}
    (hperm : List.Perm f g) :
    SupportGroupsKeyMatchedCNFPerm
      (groupClausesByCanonicalSupport f)
      (groupClausesByCanonicalSupport g) := by
  intro sourceGroup hsourceMem
  have hsourceKeyMem :
      List.Mem sourceGroup.1
        (groupKeys (groupClausesByCanonicalSupport f)) := by
    unfold groupKeys
    exact List.mem_map_of_mem Prod.fst hsourceMem
  have htargetKeyMem :
      List.Mem sourceGroup.1
        (groupKeys (groupClausesByCanonicalSupport g)) :=
    (groupKeys_groupClausesByCanonicalSupport_perm_of_perm hperm).subset
      hsourceKeyMem
  cases exists_group_of_mem_groupKeys htargetKeyMem with
  | intro targetGroup htarget =>
      have htargetMem : List.Mem targetGroup (groupClausesByCanonicalSupport g) :=
        htarget.1
      have htargetKey : targetGroup.1 = sourceGroup.1 :=
        htarget.2
      have hsourceSelect :
          List.Perm
            (groupClausesForKey sourceGroup.1
              (groupClausesByCanonicalSupport f))
            sourceGroup.2 :=
        groupClausesForKey_perm_of_mem_group_nodup
          (nodup_groupKeys_groupClausesByCanonicalSupport f)
          hsourceMem
      have htargetSelectRaw :
          List.Perm
            (groupClausesForKey targetGroup.1
              (groupClausesByCanonicalSupport g))
            targetGroup.2 :=
        groupClausesForKey_perm_of_mem_group_nodup
          (nodup_groupKeys_groupClausesByCanonicalSupport g)
          htargetMem
      have htargetSelect :
          List.Perm
            (groupClausesForKey sourceGroup.1
              (groupClausesByCanonicalSupport g))
            targetGroup.2 := by
        rw [← htargetKey]
        exact htargetSelectRaw
      have hcontent :
          List.Perm
            (groupClausesForKey sourceGroup.1
              (groupClausesByCanonicalSupport f))
            (groupClausesForKey sourceGroup.1
              (groupClausesByCanonicalSupport g)) :=
        groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm
          sourceGroup.1 hperm
      exact
        Exists.intro targetGroup
          (And.intro htargetMem
            (And.intro htargetKey
              (List.Perm.trans htargetSelect.symm
                (List.Perm.trans hcontent.symm hsourceSelect))))

/-- Every support group in a list stores a nonempty CNF. -/
def SupportGroupsHaveNonemptyCNF {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) : Prop :=
  forall group : CanonicalSupportClauseGroup m,
    List.Mem group groups ->
      exists c : CNFModel.Clause m,
        exists tail : CNFModel.CNF m, group.2 = c :: tail

/-- Inserting one clause preserves nonemptiness of all support-group CNFs. -/
theorem supportGroupsHaveNonemptyCNF_insertClauseByCanonicalSupport
    {m : Nat}
    (c : CNFModel.Clause m)
    {groups : List (CanonicalSupportClauseGroup m)}
    (hgroups : SupportGroupsHaveNonemptyCNF groups) :
    SupportGroupsHaveNonemptyCNF
      (insertClauseByCanonicalSupport c groups) := by
  induction groups with
  | nil =>
      intro group hmem
      have hmem' :
          List.Mem group [(canonicalClauseSupportKey c, [c])] := by
        simpa [insertClauseByCanonicalSupport] using hmem
      cases hmem' with
      | head =>
          exact Exists.intro c (Exists.intro [] rfl)
      | tail _ hnil =>
          cases hnil
  | cons head groups ih =>
      intro group hmem
      by_cases hkey : canonicalClauseSupportKey c = head.1
      case pos =>
        have hmem' :
            List.Mem group ((head.1, head.2 ++ [c]) :: groups) := by
          simpa [insertClauseByCanonicalSupport, hkey] using hmem
        cases hmem' with
        | head =>
            rcases hgroups head (List.Mem.head groups) with
              ⟨headClause, headTail, hhead⟩
            exact
              Exists.intro headClause
                (Exists.intro (headTail ++ [c]) (by simp [hhead]))
        | tail _ htail =>
            exact hgroups group (List.Mem.tail head htail)
      case neg =>
        have hmem' :
            List.Mem group
              (head :: insertClauseByCanonicalSupport c groups) := by
          simpa [insertClauseByCanonicalSupport, hkey] using hmem
        cases hmem' with
        | head =>
            exact hgroups head (List.Mem.head groups)
        | tail _ htail =>
            have htailGroups : SupportGroupsHaveNonemptyCNF groups := by
              intro group hgroup
              exact hgroups group (List.Mem.tail head hgroup)
            exact ih htailGroups group htail

/-- Folding clauses into support groups preserves nonemptiness of group CNFs. -/
theorem supportGroupsHaveNonemptyCNF_fold_insert
    {m : Nat}
    (f : CNFModel.CNF m)
    {groups : List (CanonicalSupportClauseGroup m)}
    (hgroups : SupportGroupsHaveNonemptyCNF groups) :
    SupportGroupsHaveNonemptyCNF
      (f.foldl
        (fun groups c => insertClauseByCanonicalSupport c groups)
        groups) := by
  induction f generalizing groups with
  | nil =>
      exact hgroups
  | cons c _f ih =>
      exact ih
        (supportGroupsHaveNonemptyCNF_insertClauseByCanonicalSupport
          c hgroups)

/-- The executable support grouper emits only nonempty support-group CNFs. -/
theorem supportGroupsHaveNonemptyCNF_groupClausesByCanonicalSupport
    {m : Nat}
    (f : CNFModel.CNF m) :
    SupportGroupsHaveNonemptyCNF (groupClausesByCanonicalSupport f) := by
  unfold groupClausesByCanonicalSupport
  apply supportGroupsHaveNonemptyCNF_fold_insert
  intro group hmem
  cases hmem

/-- Any support group emitted by the executable grouper has a cons-form CNF. -/
theorem supportGroupCNF_exists_cons_of_mem_groupClausesByCanonicalSupport
    {m : Nat}
    {f : CNFModel.CNF m}
    {group : CanonicalSupportClauseGroup m}
    (hgroup : List.Mem group (groupClausesByCanonicalSupport f)) :
    exists c : CNFModel.Clause m,
      exists tail : CNFModel.CNF m, group.2 = c :: tail :=
  supportGroupsHaveNonemptyCNF_groupClausesByCanonicalSupport f group hgroup

/-- A list permuted from a cons-form CNF is also cons-form. -/
theorem cnf_exists_cons_of_perm_cons
    {m : Nat}
    {target source : CNFModel.CNF m}
    {sourceHead : CNFModel.Clause m}
    {sourceTail : CNFModel.CNF m}
    (hperm : List.Perm target source)
    (hsource : source = sourceHead :: sourceTail) :
    exists targetHead : CNFModel.Clause m,
      exists targetTail : CNFModel.CNF m, target = targetHead :: targetTail := by
  cases target with
  | nil =>
      have hlen := hperm.length_eq
      simp [hsource] at hlen
  | cons targetHead targetTail =>
      exact Exists.intro targetHead (Exists.intro targetTail rfl)

/--
Key-matched support groups can be reordered into a component-wise aligned
target list.  This is the bridge from unordered support-key matching to the
aligned transport theorem: source group keys drive the target order, while each
target component carries a clause-list permutation of its source component.
-/
theorem exists_alignedSupportGroupCNFPermNonempty_of_keyMatched
    {m : Nat}
    {sourceGroups targetGroups : List (CanonicalSupportClauseGroup m)}
    (hsourceNodup : (groupKeys sourceGroups).Nodup)
    (hkeys :
      List.Perm (groupKeys sourceGroups) (groupKeys targetGroups))
    (hsourceNonempty : SupportGroupsHaveNonemptyCNF sourceGroups)
    (hmatched : SupportGroupsKeyMatchedCNFPerm sourceGroups targetGroups) :
    exists alignedTargetGroups : List (CanonicalSupportClauseGroup m),
      List.Perm targetGroups alignedTargetGroups /\
        AlignedSupportGroupCNFPermNonempty
          sourceGroups alignedTargetGroups := by
  induction sourceGroups generalizing targetGroups with
  | nil =>
      cases targetGroups with
      | nil =>
          exact Exists.intro [] (And.intro (List.Perm.refl []) True.intro)
      | cons targetGroup targetGroups =>
          have hlen := hkeys.length_eq
          simp [groupKeys] at hlen
  | cons sourceGroup sourceGroups ih =>
      have hnodupCons :
          (sourceGroup.1 :: groupKeys sourceGroups).Nodup := by
        simpa [groupKeys] using hsourceNodup
      have hsourceTailNodup : (groupKeys sourceGroups).Nodup :=
        (List.nodup_cons.mp hnodupCons).2
      have hsourceHeadFresh :
          Not (List.Mem sourceGroup.1 (groupKeys sourceGroups)) :=
        (List.nodup_cons.mp hnodupCons).1
      rcases hmatched sourceGroup (List.Mem.head sourceGroups) with
        ⟨targetGroup, htargetMem, htargetKey, htargetPerm⟩
      rcases hsourceNonempty sourceGroup (List.Mem.head sourceGroups) with
        ⟨sourceHead, sourceTail, hsourceCons⟩
      rcases cnf_exists_cons_of_perm_cons htargetPerm hsourceCons with
        ⟨targetHead, targetTail, htargetCons⟩
      rcases List.append_of_mem htargetMem with
        ⟨targetPrefix, targetSuffix, htargetSplit⟩
      let targetRest : List (CanonicalSupportClauseGroup m) :=
        targetPrefix ++ targetSuffix
      have htargetGroupsPerm :
          List.Perm targetGroups (targetGroup :: targetRest) := by
        rw [htargetSplit]
        exact List.perm_middle
      have htargetKeysPerm :
          List.Perm (groupKeys targetGroups)
            (targetGroup.1 :: groupKeys targetRest) := by
        simpa [groupKeys] using htargetGroupsPerm.map Prod.fst
      have hsourceToTargetKeys :
          List.Perm (sourceGroup.1 :: groupKeys sourceGroups)
            (targetGroup.1 :: groupKeys targetRest) := by
        exact List.Perm.trans (by simpa [groupKeys] using hkeys)
          htargetKeysPerm
      have hsourceToTargetKeysSameHead :
          List.Perm (sourceGroup.1 :: groupKeys sourceGroups)
            (sourceGroup.1 :: groupKeys targetRest) := by
        simpa [htargetKey] using hsourceToTargetKeys
      have htailKeys :
          List.Perm (groupKeys sourceGroups)
            (groupKeys targetRest) :=
        List.Perm.cons_inv hsourceToTargetKeysSameHead
      have hsourceTailNonempty :
          SupportGroupsHaveNonemptyCNF sourceGroups := by
        intro group hgroup
        exact hsourceNonempty group (List.Mem.tail sourceGroup hgroup)
      have hmatchedTail :
          SupportGroupsKeyMatchedCNFPerm sourceGroups
            targetRest := by
        intro sourceTailGroup hsourceTailMem
        rcases hmatched sourceTailGroup
            (List.Mem.tail sourceGroup hsourceTailMem) with
          ⟨targetTailGroup, htargetTailMem, htargetTailKey,
            htargetTailPerm⟩
        have htailKeyMem :
            List.Mem sourceTailGroup.1 (groupKeys sourceGroups) := by
          unfold groupKeys
          exact List.mem_map_of_mem Prod.fst hsourceTailMem
        have hneq : targetTailGroup ≠ targetGroup := by
          intro heq
          subst targetTailGroup
          have hsourceKeyEq : sourceGroup.1 = sourceTailGroup.1 := by
            calc
              sourceGroup.1 = targetGroup.1 := htargetKey.symm
              _ = sourceTailGroup.1 := htargetTailKey
          exact hsourceHeadFresh (by
            rw [hsourceKeyEq]
            exact htailKeyMem)
        have htargetTailMemSplit :
            List.Mem targetTailGroup
              (targetPrefix ++ targetGroup :: targetSuffix) := by
          simpa [htargetSplit] using htargetTailMem
        have htargetTailMemRest : List.Mem targetTailGroup targetRest := by
          unfold targetRest
          cases List.mem_append.mp htargetTailMemSplit with
          | inl hprefix =>
              exact List.mem_append.mpr (Or.inl hprefix)
          | inr hcons =>
              cases hcons with
              | head =>
                  exact False.elim (hneq rfl)
              | tail _ hsuffix =>
                  exact List.mem_append.mpr (Or.inr hsuffix)
        exact
          Exists.intro targetTailGroup
            (And.intro htargetTailMemRest
              (And.intro htargetTailKey htargetTailPerm))
      rcases ih hsourceTailNodup htailKeys hsourceTailNonempty
          hmatchedTail with
        ⟨alignedTail, htailPerm, htailAligned⟩
      exact
        Exists.intro (targetGroup :: alignedTail)
          (And.intro
            (List.Perm.trans htargetGroupsPerm
              (List.Perm.cons targetGroup htailPerm))
            (And.intro
              (Exists.intro sourceHead
                (Exists.intro sourceTail
                  (Exists.intro targetHead
                    (Exists.intro targetTail
                      (And.intro htargetPerm
                        (And.intro hsourceCons htargetCons))))))
              htailAligned))

/--
Recognition evidence for a group list gives a recognizer hit for any member
group, paired with the corresponding emitted block.
-/
theorem groupsRecognized_exists_block_of_mem
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    {group : CanonicalSupportClauseGroup m}
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized groups blocks)
    (hmem : List.Mem group groups) :
    exists block : CanonicalFingerprintRecognizedParityBlock m,
      List.Mem block blocks /\
        inferCanonicalParityBlock group.2 = some block := by
  induction groups generalizing blocks with
  | nil =>
      cases hmem
  | cons head groups ih =>
      cases blocks with
      | nil =>
          cases hrecognized
      | cons block blocks =>
          cases hmem with
          | head =>
              exact Exists.intro block
                (And.intro (List.Mem.head blocks) hrecognized.1)
          | tail _ htail =>
              rcases ih hrecognized.2 htail with
                ⟨tailBlock, htailMem, htailInfer⟩
              exact Exists.intro tailBlock
                (And.intro (List.Mem.tail block htailMem) htailInfer)

/--
Recognition evidence transports across a key-matched component relation.

This is the residual-free half of whole-CNF interleaving.  It proves that if
each target component can be matched to a source component with the same key and
permuted clause content, then every target component is recognized whenever the
source components were recognized.  It does not yet assert a permutation
relation for the emitted compact GF(2) list.
-/
theorem groupsRecognized_transport_of_keyMatchedCNFPerm
    {m : Nat}
    {source : CNFModel.CNF m}
    {sourceGroups targetGroups : List (CanonicalSupportClauseGroup m)}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hfrom : SupportGroupsFromGrouper source sourceGroups)
    (hmatched : SupportGroupsKeyMatchedCNFPerm targetGroups sourceGroups)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized sourceGroups sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized targetGroups targetBlocks := by
  induction targetGroups with
  | nil =>
      exact Exists.intro [] True.intro
  | cons targetGroup targetGroups ih =>
      rcases hmatched targetGroup (List.Mem.head targetGroups) with
        ⟨sourceGroup, hsourceMem, _hkey, hperm⟩
      have hsourceFromGrouper :
          List.Mem sourceGroup (groupClausesByCanonicalSupport source) :=
        hfrom sourceGroup hsourceMem
      rcases groupsRecognized_exists_block_of_mem hrecognized hsourceMem with
        ⟨sourceBlock, _hsourceBlockMem, hsourceInfer⟩
      rcases
        supportGroupCNF_exists_cons_of_mem_groupClausesByCanonicalSupport
          hsourceFromGrouper with
        ⟨sourceHead, sourceTail, hsourceCons⟩
      rcases cnf_exists_cons_of_perm_cons hperm.symm hsourceCons with
        ⟨targetHead, targetTail, htargetCons⟩
      rcases
        inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons
          hsourceFromGrouper hperm.symm hsourceCons htargetCons hsourceInfer with
        ⟨targetBlock, htargetInfer, _htransport⟩
      have hmatchedTail :
          SupportGroupsKeyMatchedCNFPerm targetGroups sourceGroups := by
        intro group hgroup
        exact hmatched group (List.Mem.tail targetGroup hgroup)
      rcases ih hmatchedTail with
        ⟨targetBlocks, htargetRecognizedTail⟩
      exact
        Exists.intro (targetBlock :: targetBlocks)
          (And.intro htargetInfer htargetRecognizedTail)

/--
Residual-free splitter output transports across a key-matched component
relation.  The compact GF(2) output ordering/content relation is intentionally
left to a later theorem.
-/
theorem splitCanonicalSupportClauseGroups_residualFree_of_keyMatchedCNFPerm
    {m : Nat}
    {source : CNFModel.CNF m}
    {sourceGroups targetGroups : List (CanonicalSupportClauseGroup m)}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hfrom : SupportGroupsFromGrouper source sourceGroups)
    (hmatched : SupportGroupsKeyMatchedCNFPerm targetGroups sourceGroups)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized sourceGroups sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      splitCanonicalSupportClauseGroups targetGroups =
        { blocks := targetBlocks, residualCNF := [] } := by
  rcases
    groupsRecognized_transport_of_keyMatchedCNFPerm
      hfrom hmatched hrecognized with
    ⟨targetBlocks, htargetRecognized⟩
  exact Exists.intro targetBlocks
    (ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
      htargetRecognized)

/--
Arbitrary whole-CNF permutation preserves residual-free recognition of the
executable support-group output.  This is the first end-to-end functional
interleaving theorem for the canonical splitter, without yet identifying the
permuted compact GF(2) output.
-/
theorem groupsRecognized_groupClausesByCanonicalSupport_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport target) targetBlocks :=
  groupsRecognized_transport_of_keyMatchedCNFPerm
    (supportGroupsFromGrouper_self source)
    (supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm
      hperm.symm)
    hrecognized

/--
Arbitrary whole-CNF permutation preserves recognized compact GF(2) output up to
`List.Perm`. The proof first reorders the target support groups into the source
support-key order, transports recognition component-wise, then transports back
along the executable target group order.
-/
theorem groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport target) targetBlocks /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 targetBlocks)
          (canonicalFingerprintRecognizedBlocksGF2 sourceBlocks) := by
  rcases
    exists_alignedSupportGroupCNFPermNonempty_of_keyMatched
      (nodup_groupKeys_groupClausesByCanonicalSupport source)
      (groupKeys_groupClausesByCanonicalSupport_perm_of_perm hperm)
      (supportGroupsHaveNonemptyCNF_groupClausesByCanonicalSupport source)
      (supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm
        hperm) with
    ⟨alignedTargetGroups, htargetGroupPerm, haligned⟩
  rcases
    groupsRecognized_transport_of_alignedGroupCNFPerm
      (supportGroupsFromGrouper_self source)
      haligned hrecognized with
    ⟨alignedBlocks, halignedRecognized, halignedTransport⟩
  have halignedGF2 :
      canonicalFingerprintRecognizedBlocksGF2 alignedBlocks =
        canonicalFingerprintRecognizedBlocksGF2 sourceBlocks :=
    canonicalFingerprintRecognizedBlocksGF2_eq_of_recognizedBlocksTransport
      halignedTransport
  rcases
    groupsRecognized_transport_of_group_perm
      htargetGroupPerm halignedRecognized with
    ⟨targetBlocks, htargetRecognized, htargetGF2⟩
  exact
    Exists.intro targetBlocks
      (And.intro htargetRecognized
        (List.Perm.trans htargetGF2
          (by rw [halignedGF2])))

/--
Arbitrary whole-CNF permutation preserves residual-freeness of the executable
canonical splitter whenever the source support groups were fully recognized.
-/
theorem splitCanonicalSupportClauseGroups_residualFree_groupClausesByCanonicalSupport_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      splitCanonicalSupportClauseGroups (groupClausesByCanonicalSupport target) =
        { blocks := targetBlocks, residualCNF := [] } :=
  splitCanonicalSupportClauseGroups_residualFree_of_keyMatchedCNFPerm
    (supportGroupsFromGrouper_self source)
    (supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm
      hperm.symm)
    hrecognized

/--
Arbitrary whole-CNF permutation preserves residual-freeness and compact GF(2)
output up to `List.Perm` for the executable canonical support-group splitter.
-/
theorem splitCanonicalSupportClauseGroups_gf2_perm_groupClausesByCanonicalSupport_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      splitCanonicalSupportClauseGroups (groupClausesByCanonicalSupport target) =
        { blocks := targetBlocks, residualCNF := [] } /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 targetBlocks)
          (canonicalFingerprintRecognizedBlocksGF2 sourceBlocks) := by
  rcases
    groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm
      hperm hrecognized with
    ⟨targetBlocks, htargetRecognized, hgf2⟩
  exact
    Exists.intro targetBlocks
      (And.intro
        (ExtractorCompleteness.splitCanonicalSupportClauseGroups_of_groupsRecognized
          htargetRecognized)
        hgf2)

/--
Arbitrary whole-CNF permutation preserves residual-freeness of the full
canonical splitter whenever the source support groups were fully recognized.
-/
theorem splitArityFourParityCanonicalSupportGroups_residualFree_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      splitArityFourParityCanonicalSupportGroups target =
        { blocks := targetBlocks, residualCNF := [] } := by
  simpa [splitArityFourParityCanonicalSupportGroups] using
    splitCanonicalSupportClauseGroups_residualFree_groupClausesByCanonicalSupport_of_perm
      hperm hrecognized

/--
Arbitrary whole-CNF permutation preserves residual-freeness and compact GF(2)
output up to `List.Perm` for the full canonical splitter.
-/
theorem splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks) :
    exists targetBlocks : List (CanonicalFingerprintRecognizedParityBlock m),
      splitArityFourParityCanonicalSupportGroups target =
        { blocks := targetBlocks, residualCNF := [] } /\
        List.Perm
          (canonicalFingerprintRecognizedBlocksGF2 targetBlocks)
          (canonicalFingerprintRecognizedBlocksGF2 sourceBlocks) := by
  simpa [splitArityFourParityCanonicalSupportGroups] using
    splitCanonicalSupportClauseGroups_gf2_perm_groupClausesByCanonicalSupport_of_perm
      hperm hrecognized

/--
Arbitrary whole-CNF permutation lifts the splitter-output theorem to the public
`ExtractorCompleteOn` surface for any caller-supplied compact GF(2) target
matching the source blocks up to `List.Perm`.
-/
theorem extractorCompleteOn_groupClausesByCanonicalSupport_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks)
    (hgf2 :
      List.Perm
        (canonicalFingerprintRecognizedBlocksGF2 sourceBlocks) s) :
    ExtractorCompleteness.ExtractorCompleteOn target s := by
  rcases
    splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm
      hperm hrecognized with
    ⟨targetBlocks, hsplit, htargetGF2⟩
  exact
    ⟨targetBlocks, hsplit, List.Perm.trans htargetGF2 hgf2⟩

/--
If the source CNF is semantically equivalent to the compact GF(2) target, then
arbitrary whole-CNF permutation preserves the combined semantic/executable
extractor-completeness surface.
-/
theorem semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm
    {m : Nat}
    {source target : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    {sourceBlocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hperm : List.Perm source target)
    (hsem :
      forall a : CNFModel.Assignment m,
        CNFModel.cnfSat a source <->
          ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a s)
    (hrecognized :
      ExtractorCompleteness.GroupsRecognized
        (groupClausesByCanonicalSupport source) sourceBlocks)
    (hgf2 :
      List.Perm
        (canonicalFingerprintRecognizedBlocksGF2 sourceBlocks) s) :
    ExtractorCompleteness.SemanticExtractorCompleteOn target s := by
  constructor
  case left =>
    intro a
    exact Iff.trans (cnfSat_iff_of_perm (a := a) hperm.symm) (hsem a)
  case right =>
    exact
      extractorCompleteOn_groupClausesByCanonicalSupport_of_perm
        hperm hrecognized hgf2

/--
Clause-key disjointness implies the fresh-key premise required by the frame
theorem.
-/
theorem cnfKeysFreshForGroups_of_clauseKeysDisjoint
    {m : Nat}
    (f g : CNFModel.CNF m)
    (hdisjoint : CNFClauseKeysDisjoint f g) :
    CNFKeysFreshForGroups g (groupClausesByCanonicalSupport f) := by
  intro cg hcg hmem
  have hfrom :=
    mem_groupKeys_groupClausesByCanonicalSupport f hmem
  cases hfrom with
  | intro cf hcfAnd =>
      cases hcfAnd with
      | intro hcf hkey =>
          exact hdisjoint cf hcf cg hcg hkey

/--
Grouping commutes with append under the operational clause-key disjointness
predicate.
-/
theorem groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
    {m : Nat}
    (f g : CNFModel.CNF m)
    (hdisjoint : CNFClauseKeysDisjoint f g) :
    groupClausesByCanonicalSupport (f ++ g) =
      groupClausesByCanonicalSupport f ++
        groupClausesByCanonicalSupport g :=
  groupClausesByCanonicalSupport_append_of_fresh f g
    (cnfKeysFreshForGroups_of_clauseKeysDisjoint f g hdisjoint)

/--
Grouping commutes with append after independently permuting the two fragments,
provided the original fragments were clause-key disjoint.
-/
theorem groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint_perm
    {m : Nat}
    {f f' g g' : CNFModel.CNF m}
    (hfperm : List.Perm f' f)
    (hgperm : List.Perm g' g)
    (hdisjoint : CNFClauseKeysDisjoint f g) :
    groupClausesByCanonicalSupport (f' ++ g') =
      groupClausesByCanonicalSupport f' ++
        groupClausesByCanonicalSupport g' :=
  groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint f' g'
    (cnfClauseKeysDisjoint_of_perm hfperm hgperm hdisjoint)

/--
Grouping commutes with append under ordinary variable-disjoint support, provided
the right-hand CNF has no empty-support clauses.
-/
theorem groupClausesByCanonicalSupport_append_of_disjointSupport
    {m : Nat}
    (f g : CNFModel.CNF m)
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : CNFClausesHaveNonemptySupport g) :
    groupClausesByCanonicalSupport (f ++ g) =
      groupClausesByCanonicalSupport f ++
        groupClausesByCanonicalSupport g :=
  groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint f g
    (clauseKeysDisjoint_of_disjointSupport f g hdisjoint hnonempty)

/--
Exact baseline splitter frame under operational canonical-support-key
disjointness.  If each fragment is already residual-free with known emitted
blocks, then splitting the append emits exactly the left blocks followed by the
right blocks and leaves no residual CNF.
-/
theorem splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := leftBlocks, residualCNF := [] })
    (hright :
      splitArityFourParityCanonicalSupportGroups g =
        { blocks := rightBlocks, residualCNF := [] }) :
    splitArityFourParityCanonicalSupportGroups (f ++ g) =
      { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } := by
  unfold splitArityFourParityCanonicalSupportGroups at hleft hright
  unfold splitArityFourParityCanonicalSupportGroups
  rw [groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint f g hdisjoint]
  exact
    ExtractorCompleteness.splitCanonicalSupportClauseGroups_append_of_residual_free
      hleft hright

/--
Exact baseline splitter frame after independently permuting the two fragments,
provided the original fragments were clause-key disjoint.
-/
theorem splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint_perm
    {m : Nat} {f f' g g' : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hfperm : List.Perm f' f)
    (hgperm : List.Perm g' g)
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft :
      splitArityFourParityCanonicalSupportGroups f' =
        { blocks := leftBlocks, residualCNF := [] })
    (hright :
      splitArityFourParityCanonicalSupportGroups g' =
        { blocks := rightBlocks, residualCNF := [] }) :
    splitArityFourParityCanonicalSupportGroups (f' ++ g') =
      { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } :=
  splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint
    (cnfClauseKeysDisjoint_of_perm hfperm hgperm hdisjoint)
    hleft hright

/--
Exact baseline splitter frame under ordinary variable-disjoint support, with
the same nonempty-right-CNF side condition required by the grouping frame.
-/
theorem splitArityFourParityCanonicalSupportGroups_append_of_disjointSupport
    {m : Nat} {f g : CNFModel.CNF m}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : CNFClausesHaveNonemptySupport g)
    (hleft :
      splitArityFourParityCanonicalSupportGroups f =
        { blocks := leftBlocks, residualCNF := [] })
    (hright :
      splitArityFourParityCanonicalSupportGroups g =
        { blocks := rightBlocks, residualCNF := [] }) :
    splitArityFourParityCanonicalSupportGroups (f ++ g) =
      { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } :=
  splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint
    (clauseKeysDisjoint_of_disjointSupport f g hdisjoint hnonempty)
    hleft hright

/--
Residual-free extractor completeness composes under operational
canonical-support-key disjointness.
-/
theorem extractorCompleteOn_append_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft : ExtractorCompleteness.ExtractorCompleteOn f s)
    (hright : ExtractorCompleteness.ExtractorCompleteOn g t) :
    ExtractorCompleteness.ExtractorCompleteOn (f ++ g) (List.append s t) :=
  ExtractorCompleteness.extractorCompleteOn_append_of_groupAppend
    (groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
      f g hdisjoint)
    hleft hright

/--
Residual-free extractor completeness composes under ordinary variable-disjoint
support when the right-hand CNF has no empty-support clauses.
-/
theorem extractorCompleteOn_append_of_disjointSupport
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : CNFClausesHaveNonemptySupport g)
    (hleft : ExtractorCompleteness.ExtractorCompleteOn f s)
    (hright : ExtractorCompleteness.ExtractorCompleteOn g t) :
    ExtractorCompleteness.ExtractorCompleteOn (f ++ g) (List.append s t) :=
  extractorCompleteOn_append_of_clauseKeysDisjoint
    (clauseKeysDisjoint_of_disjointSupport f g hdisjoint hnonempty)
    hleft hright

/--
Residual-free extractor completeness composes after independently permuting the
two fragments, provided the original fragments were clause-key disjoint.
-/
theorem extractorCompleteOn_append_of_clauseKeysDisjoint_perm
    {m : Nat} {f f' g g' : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hfperm : List.Perm f' f)
    (hgperm : List.Perm g' g)
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft : ExtractorCompleteness.ExtractorCompleteOn f' s)
    (hright : ExtractorCompleteness.ExtractorCompleteOn g' t) :
    ExtractorCompleteness.ExtractorCompleteOn (f' ++ g') (List.append s t) :=
  extractorCompleteOn_append_of_clauseKeysDisjoint
    (cnfClauseKeysDisjoint_of_perm hfperm hgperm hdisjoint)
    hleft hright

/--
Residual-free extractor completeness also composes in swapped append order.
The emitted GF(2) equations are transported back to the caller's original
`s ++ t` target by list permutation.
-/
theorem extractorCompleteOn_append_comm_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft : ExtractorCompleteness.ExtractorCompleteOn f s)
    (hright : ExtractorCompleteness.ExtractorCompleteOn g t) :
    ExtractorCompleteness.ExtractorCompleteOn (g ++ f) (List.append s t) := by
  have hswap :
      ExtractorCompleteness.ExtractorCompleteOn (g ++ f) (List.append t s) :=
    extractorCompleteOn_append_of_clauseKeysDisjoint
      (cnfClauseKeysDisjoint_symm hdisjoint) hright hleft
  exact
    ExtractorCompleteness.extractorCompleteOn_gf2_perm
      (List.perm_append_comm : List.Perm (t ++ s) (s ++ t))
      hswap

/--
Combined semantic/executable extraction composes under operational
canonical-support-key disjointness.
-/
theorem semanticExtractorCompleteOn_append_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft : ExtractorCompleteness.SemanticExtractorCompleteOn f s)
    (hright : ExtractorCompleteness.SemanticExtractorCompleteOn g t) :
    ExtractorCompleteness.SemanticExtractorCompleteOn (f ++ g) (List.append s t) :=
  ExtractorCompleteness.semanticExtractorCompleteOn_append_of_groupAppend
    (groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint
      f g hdisjoint)
    hleft hright

/--
Combined semantic/executable extraction composes under ordinary
variable-disjoint support when the right-hand CNF has no empty-support clauses.
-/
theorem semanticExtractorCompleteOn_append_of_disjointSupport
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : ParityEncoded.DisjointSupport f g)
    (hnonempty : CNFClausesHaveNonemptySupport g)
    (hleft : ExtractorCompleteness.SemanticExtractorCompleteOn f s)
    (hright : ExtractorCompleteness.SemanticExtractorCompleteOn g t) :
    ExtractorCompleteness.SemanticExtractorCompleteOn (f ++ g) (List.append s t) :=
  semanticExtractorCompleteOn_append_of_clauseKeysDisjoint
    (clauseKeysDisjoint_of_disjointSupport f g hdisjoint hnonempty)
    hleft hright

/--
Combined semantic/executable extraction composes after independently permuting
the two fragments, provided the original fragments were clause-key disjoint.
-/
theorem semanticExtractorCompleteOn_append_of_clauseKeysDisjoint_perm
    {m : Nat} {f f' g g' : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hfperm : List.Perm f' f)
    (hgperm : List.Perm g' g)
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft : ExtractorCompleteness.SemanticExtractorCompleteOn f' s)
    (hright : ExtractorCompleteness.SemanticExtractorCompleteOn g' t) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (f' ++ g') (List.append s t) :=
  semanticExtractorCompleteOn_append_of_clauseKeysDisjoint
    (cnfClauseKeysDisjoint_of_perm hfperm hgperm hdisjoint)
    hleft hright

/--
Combined semantic/executable extraction also composes in swapped append order,
with the GF(2) target transported back to the original caller order.
-/
theorem semanticExtractorCompleteOn_append_comm_of_clauseKeysDisjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisjoint : CNFClauseKeysDisjoint f g)
    (hleft : ExtractorCompleteness.SemanticExtractorCompleteOn f s)
    (hright : ExtractorCompleteness.SemanticExtractorCompleteOn g t) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (g ++ f) (List.append s t) := by
  have hswap :
      ExtractorCompleteness.SemanticExtractorCompleteOn
        (g ++ f) (List.append t s) :=
    semanticExtractorCompleteOn_append_of_clauseKeysDisjoint
      (cnfClauseKeysDisjoint_symm hdisjoint) hright hleft
  exact
    ExtractorCompleteness.semanticExtractorCompleteOn_gf2_perm
      (List.perm_append_comm : List.Perm (t ++ s) (s ++ t))
      hswap

/--
An assignment-forbidding clause has nonempty support whenever it was built from
a nonempty variable list and a length-matching Boolean row.
-/
theorem clauseForAssignment_nonemptySupport_of_vars_ne_nil
    {m : Nat}
    {vars : List (Fin m)}
    {bs : List Bool}
    (hvars : Not (vars = []))
    (hlen : bs.length = vars.length) :
    exists v : Fin m,
      List.Mem v
        (ParityEncoded.clauseSupport
          (clauseForAssignment vars bs)) := by
  cases vars with
  | nil =>
      exact False.elim (hvars rfl)
  | cons v vs =>
      cases bs with
      | nil =>
          cases hlen
      | cons b bs =>
          exact
            Exists.intro v
              (by
                unfold ParityEncoded.clauseSupport
                change
                  List.Mem v
                    (v ::
                      List.map (fun l => l.var)
                        (clauseForAssignment vs bs))
                exact List.Mem.head
                  (List.map (fun l => l.var)
                    (clauseForAssignment vs bs)))

/--
The inline fold used by `clausesForVertex` preserves nonempty-support clauses
when every generated row has the right length and the variable list is nonempty.
-/
theorem cnfClausesHaveNonemptySupport_foldl_clausesForVertex
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    (hvars : Not (vars = []))
    (rows : List (List Bool))
    (acc : CNFModel.CNF m)
    (hrows :
      forall bs : List Bool,
        List.Mem bs rows -> bs.length = vars.length)
    (hacc : CNFClausesHaveNonemptySupport acc) :
    CNFClausesHaveNonemptySupport
      (rows.foldl
        (fun acc bs =>
          if (parity bs == charge) = true then
            acc
          else
            acc ++ [clauseForAssignment vars bs])
        acc) := by
  induction rows generalizing acc with
  | nil =>
      exact hacc
  | cons row rows ih =>
      have htailRows :
          forall bs : List Bool,
            List.Mem bs rows -> bs.length = vars.length := by
        intro bs hbs
        exact hrows bs (List.Mem.tail row hbs)
      have hrowLen : row.length = vars.length :=
        hrows row (List.Mem.head rows)
      by_cases hgood : (parity row == charge) = true
      case pos =>
        change
          CNFClausesHaveNonemptySupport
            (rows.foldl
              (fun acc bs =>
                if (parity bs == charge) = true then
                  acc
                else
                  acc ++ [clauseForAssignment vars bs])
              (if (parity row == charge) = true then
                acc
              else
                acc ++ [clauseForAssignment vars row]))
        rw [if_pos hgood]
        exact ih acc htailRows hacc
      case neg =>
        change
          CNFClausesHaveNonemptySupport
            (rows.foldl
              (fun acc bs =>
                if (parity bs == charge) = true then
                  acc
                else
                  acc ++ [clauseForAssignment vars bs])
              (if (parity row == charge) = true then
                acc
              else
                acc ++ [clauseForAssignment vars row]))
        rw [if_neg hgood]
        apply ih
        case hrows =>
          exact htailRows
        case hacc =>
          intro c hc
          cases List.mem_append.1 hc with
          | inl hleft =>
              exact hacc c hleft
          | inr hright =>
              cases hright with
              | head =>
                  exact
                    clauseForAssignment_nonemptySupport_of_vars_ne_nil
                      hvars hrowLen
              | tail _ hnil =>
                  cases hnil

/-- Clause-complete parity expansions have nonempty clause support for nonempty variables. -/
theorem cnfClausesHaveNonemptySupport_clausesForVertex
    {m : Nat}
    {vars : List (Fin m)}
    {charge : Bool}
    (hvars : Not (vars = [])) :
    CNFClausesHaveNonemptySupport (clausesForVertex vars charge) := by
  unfold clausesForVertex
  apply cnfClausesHaveNonemptySupport_foldl_clausesForVertex
  case hvars =>
    exact hvars
  case hrows =>
    intro bs hbs
    exact length_of_mem_allAssignments hbs
  case hacc =>
    intro c hc
    cases hc

end GroupFrame
end TseitinCNFData
end CertifiedAffine
