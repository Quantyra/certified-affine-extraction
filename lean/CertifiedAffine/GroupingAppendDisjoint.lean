import CertifiedAffine.TseitinCNFData
import CertifiedAffine.ExtractorCompleteness

/-!
# Grouping homomorphism over append under canonical-support key disjointness

`groupClausesByCanonicalSupport` folds `insertClauseByCanonicalSupport` over a
clause list.  The append/gluing surface in `ExtractorCompleteness`
(`extractorCompleteOn_append_of_groupAppend`) needs the *grouping* pass to frame
an append as the concatenation of the two fragment groupings:

  `groupClausesByCanonicalSupport (f ++ g)
     = groupClausesByCanonicalSupport f ++ groupClausesByCanonicalSupport g`.

This file proves exactly that, under the natural side condition that the
canonical support keys occurring in `f` are disjoint from those occurring in `g`.

The insert behaviour (read off the definition) is:
* if some existing group already carries the clause's canonical key, the clause
  is *merged* into that group (`g.2 ++ [c]`), and
* otherwise a fresh singleton group `(key c, [c])` is *appended at the end*.

So the homomorphism statement is genuinely false in general (a `g`-clause whose
key already occurs in `f` would merge into an `f`-bucket rather than start a new
one); key disjointness is the precise hypothesis that rules this out.
-/

namespace CertifiedAffine
namespace TseitinCNFData
namespace GroupingAppendDisjoint

open scoped List

/-- The multiset (as a list) of canonical support keys carried by a grouping. -/
def groupKeys {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) : List CanonicalClauseSupportKey :=
  groups.map Prod.fst

@[simp] theorem groupKeys_nil {m : Nat} :
    groupKeys ([] : List (CanonicalSupportClauseGroup m)) = [] := rfl

@[simp] theorem groupKeys_cons {m : Nat}
    (g : CanonicalSupportClauseGroup m)
    (rest : List (CanonicalSupportClauseGroup m)) :
    groupKeys (g :: rest) = g.1 :: groupKeys rest := rfl

@[simp] theorem groupKeys_append {m : Nat}
    (A B : List (CanonicalSupportClauseGroup m)) :
    groupKeys (A ++ B) = groupKeys A ++ groupKeys B := by
  simp [groupKeys]

/--
**Frame lemma.**  If the clause's canonical key does not occur among the keys of
the prefix grouping `A`, then inserting the clause into `A ++ B` leaves `A`
untouched and inserts into `B`.
-/
theorem insertClauseByCanonicalSupport_append_of_key_not_mem
    {m : Nat} (c : CNFModel.Clause m)
    (A B : List (CanonicalSupportClauseGroup m))
    (hA : canonicalClauseSupportKey c ∉ groupKeys A) :
    insertClauseByCanonicalSupport c (A ++ B) =
      A ++ insertClauseByCanonicalSupport c B := by
  induction A with
  | nil => simp
  | cons a rest ih =>
      have hne : canonicalClauseSupportKey c ≠ a.1 := by
        intro h
        exact hA (by simp [groupKeys, h])
      have hrest : canonicalClauseSupportKey c ∉ groupKeys rest := by
        intro h
        exact hA (by simp [groupKeys] at h ⊢; exact Or.inr h)
      -- Unfold one step of insert on `(a :: rest) ++ B = a :: (rest ++ B)`.
      show insertClauseByCanonicalSupport c (a :: (rest ++ B)) =
        a :: (rest ++ insertClauseByCanonicalSupport c B)
      have hstep : insertClauseByCanonicalSupport c (a :: (rest ++ B)) =
          a :: insertClauseByCanonicalSupport c (rest ++ B) := by
        simp only [insertClauseByCanonicalSupport, hne, if_false, if_neg hne]
      rw [hstep, ih hrest]

/--
Inserting a clause whose key is absent from `A` into `A ++ B` only grows the
`B` side, so the keys of `A` are unaffected.  (Helper for the fold invariant.)
-/
theorem groupKeys_insert_subset {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m)) :
    ∀ k, k ∈ groupKeys groups →
      k ∈ groupKeys (insertClauseByCanonicalSupport c groups) := by
  induction groups with
  | nil => intro k hk; simp [groupKeys] at hk
  | cons g rest ih =>
      intro k hk
      unfold insertClauseByCanonicalSupport
      by_cases hkey : canonicalClauseSupportKey c = g.1
      · rw [if_pos hkey]
        simpa [groupKeys] using hk
      · rw [if_neg hkey]
        simp only [groupKeys, List.map_cons, List.mem_cons] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (ih k (by simpa [groupKeys] using hk))

/--
**Fold frame lemma.**  Folding the clauses of `gs` into `A ++ B` leaves the
prefix `A` untouched and folds them into `B`, provided every clause of `gs` has a
canonical key absent from `A`.
-/
theorem foldl_insertClauseByCanonicalSupport_append_of_keys_not_mem
    {m : Nat} (gs : CNFModel.CNF m)
    (A B : List (CanonicalSupportClauseGroup m))
    (hkeys : ∀ c ∈ gs, canonicalClauseSupportKey c ∉ groupKeys A) :
    gs.foldl (fun groups c => insertClauseByCanonicalSupport c groups) (A ++ B) =
      A ++ gs.foldl (fun groups c => insertClauseByCanonicalSupport c groups) B := by
  induction gs generalizing B with
  | nil => simp
  | cons c rest ih =>
      have hc : canonicalClauseSupportKey c ∉ groupKeys A :=
        hkeys c (by simp)
      have hrest : ∀ d ∈ rest, canonicalClauseSupportKey d ∉ groupKeys A :=
        fun d hd => hkeys d (by simp [hd])
      simp only [List.foldl_cons]
      rw [insertClauseByCanonicalSupport_append_of_key_not_mem c A B hc]
      exact ih (insertClauseByCanonicalSupport c B) hrest

/-- A key in `insert c groups` is either an old key of `groups` or `key c`. -/
theorem mem_groupKeys_insert {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m))
    (k : CanonicalClauseSupportKey)
    (hk : k ∈ groupKeys (insertClauseByCanonicalSupport c groups)) :
    k ∈ groupKeys groups ∨ k = canonicalClauseSupportKey c := by
  induction groups with
  | nil =>
      simp only [insertClauseByCanonicalSupport, groupKeys, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      exact Or.inr hk
  | cons g rest ih =>
      unfold insertClauseByCanonicalSupport at hk
      by_cases hkey : canonicalClauseSupportKey c = g.1
      · rw [if_pos hkey] at hk
        exact Or.inl (by simpa [groupKeys] using hk)
      · rw [if_neg hkey] at hk
        simp only [groupKeys, List.map_cons, List.mem_cons] at hk
        rcases hk with hk | hk
        · refine Or.inl ?_
          simp only [groupKeys, List.map_cons, List.mem_cons]
          exact Or.inl hk
        · rcases ih (by simpa [groupKeys] using hk) with h | h
          · refine Or.inl ?_
            simp only [groupKeys, List.map_cons, List.mem_cons]
            exact Or.inr h
          · exact Or.inr h

/-- `key c` is among the keys after inserting any clause with that key. -/
theorem mem_groupKeys_insert_of_eq {m : Nat}
    (c : CNFModel.Clause m)
    (groups : List (CanonicalSupportClauseGroup m))
    {k : CanonicalClauseSupportKey}
    (hk : canonicalClauseSupportKey c = k) :
    k ∈ groupKeys (insertClauseByCanonicalSupport c groups) := by
  induction groups with
  | nil =>
      simp [insertClauseByCanonicalSupport, groupKeys, hk]
  | cons g rest ih =>
      unfold insertClauseByCanonicalSupport
      by_cases hkey : canonicalClauseSupportKey c = g.1
      · rw [if_pos hkey]
        simp only [groupKeys, List.map_cons, List.mem_cons]
        exact Or.inl (by rw [← hkey, hk])
      · rw [if_neg hkey]
        simp only [groupKeys, List.map_cons, List.mem_cons]
        exact Or.inr ih

/--
The keys carried by a grouping of `f` are exactly the canonical keys occurring
in `f` (membership characterisation).  This turns the per-clause disjointness
hypothesis into a grouping-level "key absent" fact.
-/
theorem mem_groupKeys_groupClausesByCanonicalSupport {m : Nat}
    (f : CNFModel.CNF m) (k : CanonicalClauseSupportKey) :
    k ∈ groupKeys (groupClausesByCanonicalSupport f) ↔
      ∃ c ∈ f, canonicalClauseSupportKey c = k := by
  unfold groupClausesByCanonicalSupport
  -- Generalise the accumulator to support a fold induction.
  suffices H : ∀ (acc : List (CanonicalSupportClauseGroup m)),
      k ∈ groupKeys
          (f.foldl (fun groups c => insertClauseByCanonicalSupport c groups) acc) ↔
        k ∈ groupKeys acc ∨ ∃ c ∈ f, canonicalClauseSupportKey c = k by
    simpa using H []
  intro acc
  induction f generalizing acc with
  | nil => simp
  | cons c rest ih =>
      simp only [List.foldl_cons]
      rw [ih (insertClauseByCanonicalSupport c acc)]
      constructor
      · rintro (hmem | ⟨d, hd, hdk⟩)
        · -- key in `insert c acc`: either already in `acc`, or it is `key c`.
          rcases mem_groupKeys_insert c acc k hmem with hacc | hck
          · exact Or.inl hacc
          · exact Or.inr ⟨c, by simp, hck.symm⟩
        · exact Or.inr ⟨d, by simp [hd], hdk⟩
      · rintro (hacc | ⟨d, hd, hdk⟩)
        · exact Or.inl (groupKeys_insert_subset c acc k hacc)
        · simp only [List.mem_cons] at hd
          rcases hd with hdeq | hd
          · refine Or.inl (mem_groupKeys_insert_of_eq c acc ?_)
            rw [← hdeq]; exact hdk
          · exact Or.inr ⟨d, hd, hdk⟩

/--
**Main result.**  Under canonical-support *key disjointness* between `f` and `g`,
the grouping pass is a homomorphism over append:
the grouping of `f ++ g` is the concatenation of the groupings of `f` and `g`.

The disjointness hypothesis is the per-clause form
`∀ c ∈ f, ∀ d ∈ g, canonicalClauseSupportKey c ≠ canonicalClauseSupportKey d`,
which is exactly "the set of canonical keys occurring in `f` is disjoint from the
set occurring in `g`".
-/
theorem groupClausesByCanonicalSupport_append_of_keys_disjoint
    {m : Nat} (f g : CNFModel.CNF m)
    (hdisj : ∀ c ∈ f, ∀ d ∈ g,
      canonicalClauseSupportKey c ≠ canonicalClauseSupportKey d) :
    groupClausesByCanonicalSupport (f ++ g) =
      groupClausesByCanonicalSupport f ++ groupClausesByCanonicalSupport g := by
  -- `group (f ++ g) = g.foldl insert (group f)` by `foldl` over append.
  have hfold :
      groupClausesByCanonicalSupport (f ++ g) =
        g.foldl (fun groups c => insertClauseByCanonicalSupport c groups)
          (groupClausesByCanonicalSupport f) := by
    unfold groupClausesByCanonicalSupport
    rw [List.foldl_append]
  rw [hfold]
  -- Every `g`-clause's key is absent from `group f`'s keys (by disjointness).
  have hkeys : ∀ c ∈ g,
      canonicalClauseSupportKey c ∉ groupKeys (groupClausesByCanonicalSupport f) := by
    intro c hc hmem
    rcases (mem_groupKeys_groupClausesByCanonicalSupport f _).1 hmem with ⟨d, hd, hdk⟩
    exact hdisj d hd c hc (by rw [hdk])
  -- Apply the fold frame lemma with `A = group f`, `B = []`.
  have :=
    foldl_insertClauseByCanonicalSupport_append_of_keys_not_mem
      g (groupClausesByCanonicalSupport f) [] hkeys
  simpa [groupClausesByCanonicalSupport] using this

/--
**Step-4 corollary.**  Extractor completeness composes across two fragments whose
canonical support keys are disjoint, with no need to supply the grouping-append
hypothesis by hand: it is discharged by
`groupClausesByCanonicalSupport_append_of_keys_disjoint`.
-/
theorem extractorCompleteOn_append_of_keys_disjoint
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hdisj : ∀ c ∈ f, ∀ d ∈ g,
      canonicalClauseSupportKey c ≠ canonicalClauseSupportKey d)
    (hleft : ExtractorCompleteness.ExtractorCompleteOn f s)
    (hright : ExtractorCompleteness.ExtractorCompleteOn g t) :
    ExtractorCompleteness.ExtractorCompleteOn (f ++ g) (List.append s t) :=
  ExtractorCompleteness.extractorCompleteOn_append_of_groupAppend
    (groupClausesByCanonicalSupport_append_of_keys_disjoint f g hdisj)
    hleft hright

/--
**Non-vacuity witness.**  The disjointness hypothesis is satisfiable: any two
clause lists drawn over disjoint variable index sets satisfy it.  Concretely, for
`m = 2`, a clause mentioning only variable `0` and a clause mentioning only
variable `1` have distinct canonical support keys (`[0] ≠ [1]`), so the
hypothesis of the main lemma holds non-trivially for
`f = [[Literal 0 true]]`, `g = [[Literal 1 true]]`.
-/
example :
    ∀ c ∈ ([[(⟨⟨0, by decide⟩, true⟩ : CNFModel.Literal 2)]] : CNFModel.CNF 2),
      ∀ d ∈ ([[(⟨⟨1, by decide⟩, true⟩ : CNFModel.Literal 2)]] : CNFModel.CNF 2),
        canonicalClauseSupportKey c ≠ canonicalClauseSupportKey d := by
  decide

end GroupingAppendDisjoint
end TseitinCNFData
end CertifiedAffine
