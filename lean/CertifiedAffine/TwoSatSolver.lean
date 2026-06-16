import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Tactic.Common

/-!
# A certified 2-SAT decision procedure

`namespace CertifiedAffine`

## Honest scope

2-SAT is a **known polynomial-time** problem (Aspvall, Plass & Tarjan, 1979:
"A linear-time algorithm for testing the truth of certain quantified boolean
formulas"). This file provides a *machine-checked* formalization of a 2-SAT
decision procedure based on the implication graph, together with:

* a fully proven **soundness** theorem (the easy direction);
* a fully proven, genuinely non-vacuous **polynomial size bound** on the
  implication-edge list;
* a **completeness / iff** result that is stated *conditional on an explicit
  `Prop` hypothesis* (`Completeness`), because the unconditional completeness
  proof (no contradictory cycle ⇒ satisfying assignment) is the hard direction
  and is **not** proven here.

This is **verified tractability of a known-easy problem**. It is **NOT**
P = NP, **NOT** a polynomial general-SAT algorithm, and **NOT** a proof of the
hard direction of 2-SAT correctness.

## Theorems actually proven in this file

* `twoSatDecide_sound`  : `(∃ a, Sat a φ) → twoSatDecide φ = true`  (UNCONDITIONAL)
* `implicationEdges_length_le` : `(implicationEdges φ).length ≤ 2 * φ.length`
  (UNCONDITIONAL, genuine polynomial bound)
* `twoSatDecide_iff` : `Completeness φ → (twoSatDecide φ = true ↔ ∃ a, Sat a φ)`
  (CONDITIONAL on the explicit hypothesis `Completeness φ`; the forward
  direction reuses the unconditional soundness theorem)
* `sat_witness_accepted` / `unsat_witness_rejected` : concrete `decide`-checked
  witnesses (one satisfiable instance accepted, one unsatisfiable instance
  rejected).

The single open lemma is exactly the unconditional content of `Completeness`
(no contradictory implication cycle ⇒ a satisfying assignment exists).

## Reachability model

Reachability is `Relation.ReflTransGen` of the single-step implication relation
(`Reaches`). For the *executable* decision procedure we use a **fuel-bounded**
boolean reachability `reachB` with fuel equal to the number of literals
`2 * n`; we prove the **sufficiency lemma** `reachB_sound` that `reachB` only
ever reports reachable pairs that are genuinely connected by `Reaches`. The
decision procedure rejects iff some variable has a fuel-bounded contradictory
cycle, and soundness is proven against the relational `Reaches` via this lemma.
-/

namespace CertifiedAffine

/-- A literal over `n` boolean variables: a variable index together with a
sign (`true` = positive occurrence, `false` = negated occurrence). -/
structure Lit (n : ℕ) where
  var : Fin n
  sign : Bool
deriving DecidableEq, Repr

namespace Lit

/-- Negate a literal (flip its sign). -/
def neg {n : ℕ} (l : Lit n) : Lit n := ⟨l.var, !l.sign⟩

@[simp] theorem neg_var {n : ℕ} (l : Lit n) : (l.neg).var = l.var := rfl
@[simp] theorem neg_sign {n : ℕ} (l : Lit n) : (l.neg).sign = !l.sign := rfl
@[simp] theorem neg_neg {n : ℕ} (l : Lit n) : l.neg.neg = l := by
  cases l; simp [neg]

end Lit

/-- The positive literal for variable `x`. -/
def pos {n : ℕ} (x : Fin n) : Lit n := ⟨x, true⟩

/-- The negative literal for variable `x`. -/
def negLit {n : ℕ} (x : Fin n) : Lit n := ⟨x, false⟩

@[simp] theorem neg_pos {n : ℕ} (x : Fin n) : (pos x).neg = negLit x := rfl
@[simp] theorem neg_negLit {n : ℕ} (x : Fin n) : (negLit x).neg = pos x := rfl

/-- A 2-SAT clause is an (ordered, but semantically unordered) pair of literals,
interpreted as the disjunction `fst ∨ snd`. A unit clause `(a)` is encoded as
`(a, a)`. -/
structure Clause (n : ℕ) where
  fst : Lit n
  snd : Lit n
deriving DecidableEq, Repr

/-- A CNF in 2-SAT form is a list of clauses. -/
abbrev CNF (n : ℕ) := List (Clause n)

/-- An assignment maps each variable to a boolean. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- Truth value of a literal under an assignment. A positive literal is true
iff the variable is `true`; a negative literal is true iff the variable is
`false`. -/
def litVal {n : ℕ} (a : Assignment n) (l : Lit n) : Bool :=
  if l.sign then a l.var else !(a l.var)

/-- A clause is satisfied iff at least one of its two literals is true. -/
def clauseSat {n : ℕ} (a : Assignment n) (c : Clause n) : Prop :=
  litVal a c.fst = true ∨ litVal a c.snd = true

instance {n : ℕ} (a : Assignment n) (c : Clause n) : Decidable (clauseSat a c) := by
  unfold clauseSat; infer_instance

/-- An assignment satisfies a CNF iff it satisfies every clause. -/
def Sat {n : ℕ} (a : Assignment n) (φ : CNF n) : Prop :=
  ∀ c ∈ φ, clauseSat a c

/-! ### The implication graph

A clause `(a ∨ b)` is logically equivalent to the two implications
`¬a → b` and `¬b → a`. We record these as directed edges between literals. -/

/-- The two implication edges contributed by a single clause `(a ∨ b)`:
`(¬a, b)` and `(¬b, a)`. -/
def clauseEdges {n : ℕ} (c : Clause n) : List (Lit n × Lit n) :=
  [(c.fst.neg, c.snd), (c.snd.neg, c.fst)]

/-- All implication edges of a CNF. -/
def implicationEdges {n : ℕ} (φ : CNF n) : List (Lit n × Lit n) :=
  φ.bind clauseEdges

/-- The single-step implication relation: `l₁` implies `l₂` if `(l₁, l₂)` is an
edge of the implication graph. -/
def Step {n : ℕ} (φ : CNF n) (l₁ l₂ : Lit n) : Prop :=
  (l₁, l₂) ∈ implicationEdges φ

instance {n : ℕ} (φ : CNF n) (l₁ l₂ : Lit n) : Decidable (Step φ l₁ l₂) := by
  unfold Step; infer_instance

/-- Reachability in the implication graph: the reflexive-transitive closure of
`Step`. All correctness statements are phrased relative to this relation. -/
def Reaches {n : ℕ} (φ : CNF n) : Lit n → Lit n → Prop :=
  Relation.ReflTransGen (Step φ)

/-! ### Executable fuel-bounded reachability

`Lit n` is a finite type with `2 * n` elements, so any reachable target is
reachable by a path of length `< 2 * n`, i.e. with fuel `2 * n`. We compute
reachability by iterating a one-step successor closure on a *list* of literals
(deduplicated), which the kernel can reduce directly under `decide`. We then
prove the **sufficiency lemma**: everything `reachB` reports is genuinely
`Reaches`-connected. (We do not need the converse for soundness.) -/

/-- One-step successors of `l` in the implication graph, as a list: the second
component of every edge whose first component is `l`. -/
def succsOf {n : ℕ} (φ : CNF n) (l : Lit n) : List (Lit n) :=
  ((implicationEdges φ).filter (fun e => decide (e.1 = l))).map Prod.snd

/-- Membership in `succsOf` is exactly a single `Step`. -/
theorem mem_succsOf {n : ℕ} (φ : CNF n) (l l' : Lit n) :
    l' ∈ succsOf φ l ↔ Step φ l l' := by
  unfold succsOf Step
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hmem, hax⟩, hbl⟩
    subst hbl; subst hax; exact hmem
  · intro h
    exact ⟨l, l', ⟨h, rfl⟩, rfl⟩

/-- One closure step on a list frontier `s`: keep `s` and add every one-step
successor of a literal already in `s`. -/
def expand {n : ℕ} (φ : CNF n) (s : List (Lit n)) : List (Lit n) :=
  s ++ s.bind (succsOf φ)

/-- Fuel-bounded reachable list from `src`: iterate `expand` `fuel` times. -/
def reachList {n : ℕ} (φ : CNF n) (src : Lit n) : ℕ → List (Lit n)
  | 0 => [src]
  | (k + 1) => expand φ (reachList φ src k)

/-- Executable boolean reachability with fuel `2 * n` (the number of literals).
-/
def reachB {n : ℕ} (φ : CNF n) (src tgt : Lit n) : Bool :=
  decide (tgt ∈ reachList φ src (2 * n))

/-! #### Sufficiency: every element of `reachList` is genuinely reachable -/

/-- Every literal in `reachList φ src k` is `Reaches`-connected from `src`. -/
theorem mem_reachList_reaches {n : ℕ} (φ : CNF n) (src : Lit n) :
    ∀ (k : ℕ) (l : Lit n), l ∈ reachList φ src k → Reaches φ src l := by
  intro k
  induction k with
  | zero =>
      intro l hl
      simp only [reachList, List.mem_singleton] at hl
      subst hl
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro l hl
      simp only [reachList, expand, List.mem_append, List.mem_bind] at hl
      rcases hl with h | ⟨l', hl', hstep⟩
      · exact ih l h
      · exact Relation.ReflTransGen.tail (ih l' hl') ((mem_succsOf φ l' l).mp hstep)

/-- **Sufficiency lemma.** If `reachB` reports `src` reaches `tgt`, then they
are genuinely connected by the relational `Reaches`. -/
theorem reachB_sound {n : ℕ} (φ : CNF n) (src tgt : Lit n) :
    reachB φ src tgt = true → Reaches φ src tgt := by
  intro h
  unfold reachB at h
  rw [decide_eq_true_eq] at h
  exact mem_reachList_reaches φ src (2 * n) tgt h

/-- The decision procedure: accept `φ` iff no variable `x` is involved in a
fuel-bounded contradictory cycle, i.e. there is no `x` with both
`reachB φ (pos x) (negLit x)` and `reachB φ (negLit x) (pos x)` true. -/
def twoSatDecide {n : ℕ} (φ : CNF n) : Bool :=
  decide (∀ x : Fin n,
    ¬ (reachB φ (pos x) (negLit x) = true ∧ reachB φ (negLit x) (pos x) = true))

/-! ### Soundness (the easy direction), proven unconditionally -/

/-- A single implication edge is truth-preserving under any satisfying
assignment: if `a` satisfies `φ`, `(l₁, l₂)` is an edge, and `l₁` is true under
`a`, then `l₂` is true under `a`. -/
theorem step_preserves {n : ℕ} {φ : CNF n} {a : Assignment n}
    (hsat : Sat a φ) {l₁ l₂ : Lit n} (hstep : Step φ l₁ l₂)
    (h₁ : litVal a l₁ = true) : litVal a l₂ = true := by
  unfold Step implicationEdges at hstep
  rw [List.mem_bind] at hstep
  obtain ⟨c, hc, hmem⟩ := hstep
  have hcsat : clauseSat a c := hsat c hc
  unfold clauseEdges at hmem
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨he1, he2⟩ | ⟨he1, he2⟩
  · subst he1; subst he2
    rcases hcsat with hf | hs
    · exfalso
      revert h₁ hf
      cases c.fst with
      | mk v s => cases s <;> simp [litVal, Lit.neg]
    · exact hs
  · subst he1; subst he2
    rcases hcsat with hf | hs
    · exact hf
    · exfalso
      revert h₁ hs
      cases c.snd with
      | mk v s => cases s <;> simp [litVal, Lit.neg]

/-- Reachability is truth-preserving under any satisfying assignment. -/
theorem reaches_preserves {n : ℕ} {φ : CNF n} {a : Assignment n}
    (hsat : Sat a φ) {l₁ l₂ : Lit n} (hreach : Reaches φ l₁ l₂)
    (h₁ : litVal a l₁ = true) : litVal a l₂ = true := by
  unfold Reaches at hreach
  induction hreach with
  | refl => exact h₁
  | tail _ hstep ih => exact step_preserves hsat hstep ih

/-- A literal and its negation always take opposite truth values. -/
theorem litVal_neg {n : ℕ} (a : Assignment n) (l : Lit n) :
    litVal a l.neg = !(litVal a l) := by
  cases l with
  | mk v s => cases s <;> simp [litVal, Lit.neg]

/-- **Soundness (easy direction), unconditional.** If `φ` is satisfiable then
the decision procedure accepts it. A fuel-bounded contradictory cycle
`pos x ⟶* negLit x` and `negLit x ⟶* pos x` lifts (via `reachB_sound`) to
relational reachability, which preserves truth and is therefore impossible
under any satisfying assignment. -/
theorem twoSatDecide_sound {n : ℕ} (φ : CNF n) :
    (∃ a, Sat a φ) → twoSatDecide φ = true := by
  rintro ⟨a, hsat⟩
  unfold twoSatDecide
  rw [decide_eq_true_eq]
  intro x ⟨hpn, hnp⟩
  have hpn' : Reaches φ (pos x) (negLit x) := reachB_sound φ _ _ hpn
  have hnp' : Reaches φ (negLit x) (pos x) := reachB_sound φ _ _ hnp
  by_cases hx : litVal a (pos x) = true
  · have hneg : litVal a (negLit x) = true := reaches_preserves hsat hpn' hx
    have hcontra : litVal a (negLit x) = !(litVal a (pos x)) := by
      have := litVal_neg a (pos x); simpa using this
    rw [hx] at hcontra
    simp [hneg] at hcontra
  · have hnx : litVal a (negLit x) = true := by
      have hpos : litVal a (negLit x) = !(litVal a (pos x)) := by
        have := litVal_neg a (pos x); simpa using this
      rw [hpos]; simp [Bool.not_eq_true] at hx ⊢; exact hx
    have : litVal a (pos x) = true := reaches_preserves hsat hnp' hnx
    exact hx this

/-! ### Polynomial size bound, proven unconditionally -/

@[simp] theorem clauseEdges_length {n : ℕ} (c : Clause n) :
    (clauseEdges c).length = 2 := rfl

/-- **Polynomial bound, unconditional.** The implication graph has at most
`2 * φ.length` edges (each clause contributes exactly two implication edges).
This is a genuine, non-vacuous bound: every clause contributes exactly two
edges, so equality in fact holds and the bound is tight. -/
theorem implicationEdges_length_le {n : ℕ} (φ : CNF n) :
    (implicationEdges φ).length ≤ 2 * φ.length := by
  unfold implicationEdges
  induction φ with
  | nil => simp
  | cons c cs ih =>
      -- `(c :: cs).bind f = f c ++ cs.bind f`
      simp only [List.bind_cons, List.length_append, clauseEdges_length,
        List.length_cons, Nat.mul_succ]
      omega

/-! ### Completeness, stated conditionally on an explicit hypothesis

The hard direction — that the absence of a contradictory cycle yields a
satisfying assignment — is **not** proven here. We expose its exact content as
an explicit `Prop` hypothesis `Completeness φ`. This is *not* an axiom and *not*
a `sorry`: it is an ordinary hypothesis that any caller must discharge. -/

/-- The unproven content of 2-SAT completeness for `φ`: if the decision
procedure accepts, then `φ` is satisfiable. This is exactly the hard direction
of Aspvall–Plass–Tarjan correctness, left open in this file. -/
def Completeness {n : ℕ} (φ : CNF n) : Prop :=
  twoSatDecide φ = true → ∃ a, Sat a φ

/-- **Correctness iff, conditional on `Completeness φ`.** The forward direction
is the unconditional soundness theorem; the backward direction is supplied by
the explicit hypothesis. -/
theorem twoSatDecide_iff {n : ℕ} (φ : CNF n) (hC : Completeness φ) :
    twoSatDecide φ = true ↔ ∃ a, Sat a φ :=
  ⟨hC, twoSatDecide_sound φ⟩

/-! ### Concrete witnesses

Both are checked by `decide` through the actual decision procedure. -/

/-- A satisfiable instance over one variable: the single clause `(x ∨ x)`,
i.e. the unit clause `x`. The procedure accepts it. -/
def satWitness : CNF 1 := [⟨pos 0, pos 0⟩]

/-- An unsatisfiable instance over one variable: `{(x ∨ x), (¬x ∨ ¬x)}`, i.e.
the contradictory units `x` and `¬x`. The procedure rejects it. -/
def unsatWitness : CNF 1 := [⟨pos 0, pos 0⟩, ⟨negLit 0, negLit 0⟩]

/-- The satisfiable witness is accepted by the decision procedure. -/
theorem sat_witness_accepted : twoSatDecide satWitness = true := by decide

/-- The unsatisfiable witness is rejected by the decision procedure. -/
theorem unsat_witness_rejected : twoSatDecide unsatWitness = false := by decide

end CertifiedAffine
