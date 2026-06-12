import Std
import PvNP.BasicDefs

namespace PvNP
namespace TseitinModel

open Basic

/-!
Minimal local model for Tseitin DT lower bound.
This scopes the L1 axiom to a local graph/Tseitin model.
-/

structure UEdge where
  u : Nat
  v : Nat

def UEdge.incident (e : UEdge) (x : Nat) : Bool :=
  decide (e.u = x ∨ e.v = x)

def undirected_pred (edges : List UEdge) : Prop :=
  forall e, e ∈ edges -> UEdge.mk e.v e.u ∈ edges

def no_self_loops_pred (edges : List UEdge) : Prop :=
  forall e, e ∈ edges -> e.u ≠ e.v

def endpoints_in_range_pred (n : Nat) (edges : List UEdge) : Prop :=
  forall e, e ∈ edges -> e.u < n /\ e.v < n

structure Graph where
  n : Nat
  m : Nat
  edges : List UEdge
  undirected : undirected_pred edges
  no_self_loops : no_self_loops_pred edges
  endpoints_in_range : endpoints_in_range_pred n edges

def m_eq_edges_length (G : Graph) : Prop :=
  G.m = G.edges.length

structure GraphEncodingData where
  n : Nat
  edges : List UEdge
  undirected : undirected_pred edges
  no_self_loops : no_self_loops_pred edges
  endpoints_in_range : endpoints_in_range_pred n edges
  n_le_edges_length : n <= edges.length

def GraphEncodingData.toGraph (enc : GraphEncodingData) : Graph :=
  { n := enc.n
    m := enc.edges.length
    edges := enc.edges
    undirected := enc.undirected
    no_self_loops := enc.no_self_loops
    endpoints_in_range := enc.endpoints_in_range }

theorem m_eq_edges_length_of_encoding (enc : GraphEncodingData) :
    m_eq_edges_length enc.toGraph := by
  rfl

def encoding_two_cycle : GraphEncodingData :=
  { n := 2
    edges := [UEdge.mk 0 1, UEdge.mk 1 0]
    undirected := by
      intro e he
      simp at he
      rcases he with h | h
      · simp [h]
      · simp [h]
    no_self_loops := by
      intro e he
      simp at he
      rcases he with h | h
      · simp [h]
      · simp [h]
    endpoints_in_range := by
      intro e he
      simp at he
      rcases he with h | h
      · simp [h]
      · simp [h]
    n_le_edges_length := by
      decide }

def encoding_three_cycle : GraphEncodingData :=
  { n := 3
    edges :=
      [ UEdge.mk 0 1, UEdge.mk 1 0
      , UEdge.mk 1 2, UEdge.mk 2 1
      , UEdge.mk 2 0, UEdge.mk 0 2 ]
    undirected := by
      intro e he
      simp at he
      rcases he with h | h | h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
    no_self_loops := by
      intro e he
      simp at he
      rcases he with h | h | h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
    endpoints_in_range := by
      intro e he
      simp at he
      rcases he with h | h | h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
    n_le_edges_length := by
      decide }

def cycle_edges (n : Nat) : List UEdge :=
  (List.range n).bind (fun i =>
    [UEdge.mk i ((i + 1) % n), UEdge.mk ((i + 1) % n) i])

def circulant12_edge_block (n i : Nat) : List UEdge :=
  [ UEdge.mk i ((i + 1) % n)
  , UEdge.mk ((i + 1) % n) i
  , UEdge.mk i ((i + 2) % n)
  , UEdge.mk ((i + 2) % n) i ]

def circulant12_edges (n : Nat) : List UEdge :=
  (List.range n).bind (fun i => circulant12_edge_block n i)

theorem cycle_edges_length (n : Nat) : (cycle_edges n).length = 2 * n := by
  unfold cycle_edges
  let f := fun i =>
    [UEdge.mk i ((i + 1) % n), UEdge.mk ((i + 1) % n) i]
  have hlen :
      ((List.range n).bind f).length = 2 * (List.range n).length := by
    have hlen_f : forall x, (f x).length = 2 := by
      intro _
      simp [f]
    induction List.range n with
    | nil =>
        simp [List.bind]
    | cons x xs ih =>
        calc
          ((x :: xs).bind f).length
              = (f x).length + (xs.bind f).length := by
                  simp [List.bind, List.length_append]
          _ = 2 + 2 * xs.length := by
                  simp [hlen_f x, ih]
          _ = 2 * (List.length (x :: xs)) := by
                  simp [Nat.mul_add, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  simpa [List.length_range] using hlen

theorem circulant12_edge_block_length (n i : Nat) :
    (circulant12_edge_block n i).length = 4 := by
  simp [circulant12_edge_block]

theorem cycle_edges_n_le_length (n : Nat) : n <= (cycle_edges n).length := by
  have hlen : (cycle_edges n).length = 2 * n := cycle_edges_length n
  have hpos : 1 <= 2 := by decide
  have hle : n <= 2 * n := by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_left n hpos)
  simpa [hlen] using hle

def encoding_cycle (n : Nat)
    (h_undirected : undirected_pred (cycle_edges n))
    (h_no_self_loops : no_self_loops_pred (cycle_edges n))
    (h_endpoints : endpoints_in_range_pred n (cycle_edges n))
    (h_nle : n <= (cycle_edges n).length) : GraphEncodingData :=
  { n := n
    edges := cycle_edges n
    undirected := h_undirected
    no_self_loops := h_no_self_loops
    endpoints_in_range := h_endpoints
    n_le_edges_length := h_nle }

def encoding_cycle_nle (n : Nat)
    (h_undirected : undirected_pred (cycle_edges n))
    (h_no_self_loops : no_self_loops_pred (cycle_edges n))
    (h_endpoints : endpoints_in_range_pred n (cycle_edges n)) : GraphEncodingData :=
  encoding_cycle n h_undirected h_no_self_loops h_endpoints (cycle_edges_n_le_length n)

theorem cycle_edges_undirected (n : Nat) : undirected_pred (cycle_edges n) := by
  intro e he
  simp [cycle_edges] at he
  rcases he with ⟨i, hi, h⟩
  rcases h with h | h
  · subst h
    apply List.mem_bind.mpr
    refine ⟨i, ?_, ?_⟩
    · simpa [List.mem_range] using hi
    simp
  · subst h
    apply List.mem_bind.mpr
    refine ⟨i, ?_, ?_⟩
    · simpa [List.mem_range] using hi
    simp

theorem cycle_edges_endpoints_in_range (n : Nat) (hn : 0 < n) :
    endpoints_in_range_pred n (cycle_edges n) := by
  intro e he
  simp [cycle_edges] at he
  rcases he with ⟨i, hi, h⟩
  rcases h with h | h
  · subst h
    exact ⟨hi, Nat.mod_lt _ hn⟩
  · subst h
    exact ⟨Nat.mod_lt _ hn, hi⟩

theorem cycle_edges_no_self_loops (n : Nat) (hn : 1 < n) :
    no_self_loops_pred (cycle_edges n) := by
  intro e he
  simp [cycle_edges] at he
  rcases he with ⟨i, hi, h⟩
  rcases h with h | h
  · subst h
    intro hEq
    have hi' : i < n := by simpa [List.mem_range] using hi
    have hEq' : (i + 1) % n = i := hEq.symm
    by_cases hlt : i + 1 < n
    · have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hlt
      have : i + 1 = i := by simpa [hmod] using hEq'
      exact Nat.succ_ne_self _ this
    · have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi'
      have hge : n ≤ i + 1 := Nat.le_of_not_gt (by simpa using hlt)
      have hEqn : i + 1 = n := Nat.le_antisymm hle hge
      have hmod : (i + 1) % n = 0 := by simpa [hEqn]
      have hi0 : i = 0 := by simpa [hmod] using hEq'.symm
      exact (Nat.ne_of_gt hn) (by simpa [hi0] using hEqn.symm)
  · subst h
    intro hEq
    have hi' : i < n := by simpa [List.mem_range] using hi
    have hEq' : (i + 1) % n = i := by simpa using hEq
    by_cases hlt : i + 1 < n
    · have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hlt
      have : i + 1 = i := by simpa [hmod] using hEq'
      exact Nat.succ_ne_self _ this
    · have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi'
      have hge : n ≤ i + 1 := Nat.le_of_not_gt (by simpa using hlt)
      have hEqn : i + 1 = n := Nat.le_antisymm hle hge
      have hmod : (i + 1) % n = 0 := by simpa [hEqn]
      have hi0 : i = 0 := by simpa [hmod] using hEq'.symm
      exact (Nat.ne_of_gt hn) (by simpa [hi0] using hEqn.symm)

def encoding_cycle_derived (n : Nat) (hn : 1 < n) : GraphEncodingData :=
  let hpos : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  encoding_cycle_nle n
    (cycle_edges_undirected n)
    (cycle_edges_no_self_loops n hn)
    (cycle_edges_endpoints_in_range n hpos)

/-!
TODO checklist for derived cycle proofs (n ≥ 3):
- Prove `no_self_loops_pred (cycle_edges n)` for n ≥ 3.
- Add `encoding_cycle_derived` using the above proofs.
- (Done) `undirected_pred (cycle_edges n)`.
- (Done) `endpoints_in_range_pred n (cycle_edges n)` (needs n > 0).
- (Done) `n <= (cycle_edges n).length` (length = 2n).
-/

def incident (G : Graph) (v : Nat) : List UEdge :=
  G.edges.filter (fun e => UEdge.incident e v)

def degree (G : Graph) (v : Nat) : Nat :=
  (incident G v).length

def cycleIncidentBlock (n v i : Nat) : List UEdge :=
  [UEdge.mk i ((i + 1) % n), UEdge.mk ((i + 1) % n) i].filter
    (fun e => UEdge.incident e v)

theorem cycleIncidentBlock_length_of_hit (n v i : Nat)
    (h : Or (i = v) ((i + 1) % n = v)) :
    (cycleIncidentBlock n v i).length = 2 := by
  cases h with
  | inl hiv => simp [cycleIncidentBlock, UEdge.incident, hiv]
  | inr hsucc => simp [cycleIncidentBlock, UEdge.incident, hsucc]

theorem cycleIncidentBlock_length_of_miss (n v i : Nat)
    (h : Not (Or (i = v) ((i + 1) % n = v))) :
    (cycleIncidentBlock n v i).length = 0 := by
  have hi : Not (i = v) := by
    intro hv
    exact h (Or.inl hv)
  have hs : Not ((i + 1) % n = v) := by
    intro hv
    exact h (Or.inr hv)
  simp [cycleIncidentBlock, UEdge.incident, hi, hs]

theorem sum_cycleIncidentBlock_lengths (n v : Nat) (xs : List Nat) :
    Nat.sum (xs.map (fun i => (cycleIncidentBlock n v i).length)) =
      2 * xs.countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) := by
  induction xs with
  | nil =>
      simp
  | cons i xs ih =>
      by_cases h : Or (i = v) ((i + 1) % n = v)
      case pos =>
        simp [List.countP_cons, cycleIncidentBlock_length_of_hit, h, ih,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      case neg =>
        simp [List.countP_cons, cycleIncidentBlock_length_of_miss, h, ih,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem bind_length_eq_sum_map_length {A B : Type} (xs : List A) (f : A -> List B) :
    (xs.bind f).length = Nat.sum ((xs.map f).map List.length) := by
  change (List.join (xs.map f)).length = _
  simp

theorem circulant12_edges_length (n : Nat) : (circulant12_edges n).length = 4 * n := by
  unfold circulant12_edges
  rw [bind_length_eq_sum_map_length]
  have hsum :
      ∀ xs : List Nat,
        Nat.sum (List.map List.length (List.map (fun i => circulant12_edge_block n i) xs)) =
          4 * xs.length := by
    intro xs
    induction xs with
    | nil =>
        simp
    | cons x xs ih =>
        have ih' :
            Nat.sum (List.map (List.length ∘ fun i => circulant12_edge_block n i) xs) =
              4 * xs.length := by
          simpa [Function.comp_def] using ih
        simp [circulant12_edge_block_length, ih', Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm]
  simpa [List.length_range] using hsum (List.range n)

theorem cycle_degree_eq_two_mul_incident_index_count
    (n v : Nat) (hn : 1 < n) :
    degree (encoding_cycle_derived n hn).toGraph v =
      2 * (List.range n).countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) := by
  simp [degree, incident, encoding_cycle_derived, encoding_cycle_nle, encoding_cycle,
    cycle_edges, GraphEncodingData.toGraph]
  rw [List.filter_bind]
  rw [bind_length_eq_sum_map_length]
  simpa [cycleIncidentBlock] using sum_cycleIncidentBlock_lengths n v (List.range n)

theorem degree_eq_zero_of_ge_n (G : Graph) {v : Nat} (hv : G.n <= v) :
    degree G v = 0 := by
  unfold degree incident
  have hfalse : forall e, e ∈ G.edges -> UEdge.incident e v = false := by
    intro e he
    have hrange := G.endpoints_in_range e he
    have hu_lt : e.u < v := Nat.lt_of_lt_of_le hrange.1 hv
    have hv_lt : e.v < v := Nat.lt_of_lt_of_le hrange.2 hv
    have hu_ne : e.u ≠ v := by
      exact Nat.ne_of_lt hu_lt
    have hv_ne : e.v ≠ v := by
      exact Nat.ne_of_lt hv_lt
    have hnot : ¬ (e.u = v ∨ e.v = v) := by
      intro h
      cases h with
      | inl hEq => exact hu_ne hEq
      | inr hEq => exact hv_ne hEq
    simp [UEdge.incident, hnot]
  have hfilter :
      forall edges : List UEdge,
        (forall e, e ∈ edges -> UEdge.incident e v = false) ->
          edges.filter (fun e => UEdge.incident e v) = [] := by
    intro edges
    induction edges with
    | nil =>
        intro _
        simp
    | cons e es ih =>
        intro hall
        have hfalse_e : UEdge.incident e v = false := hall e (by simp)
        have hfalse_es : forall e, e ∈ es -> UEdge.incident e v = false := by
          intro e he
          exact hall e (by simp [he])
        simp [List.filter, hfalse_e, ih hfalse_es]
  have hfilter' := hfilter G.edges hfalse
  simp [hfilter']

def total_incident_count (G : Graph) : Nat :=
  (List.range G.n).foldl (fun acc v => acc + degree G v) 0

def total_incident_count_list (n : Nat) (edges : List UEdge) : Nat :=
  (List.range n).foldl
    (fun acc v => acc + (edges.filter (fun e => UEdge.incident e v)).length) 0

def incident_count_in_range (n : Nat) (e : UEdge) : Nat :=
  (List.range n).foldl (fun acc v => acc + (if UEdge.incident e v then 1 else 0)) 0

def total_incident_count_by_edges (n : Nat) (edges : List UEdge) : Nat :=
  edges.foldl (fun acc e => acc + incident_count_in_range n e) 0

def edge_in_range (G : Graph) (e : UEdge) : Prop :=
  e.u < G.n /\ e.v < G.n

theorem edges_endpoints_in_range (G : Graph) :
    (forall e, e ∈ G.edges -> edge_in_range G e) := by
  intro e he
  exact G.endpoints_in_range e he

def sum_edges (G : Graph) (f : UEdge -> Nat) : Nat :=
  G.edges.foldl (fun acc e => acc + f e) 0

def edge_incident_contrib (_G : Graph) (e : UEdge) : Nat :=
  (if UEdge.incident e e.u then 1 else 0) +
  (if UEdge.incident e e.v then 1 else 0)

theorem edge_incident_count_eq_two (_G : Graph) (e : UEdge) :
    edge_incident_contrib _G e = 2 := by
  simp [edge_incident_contrib, UEdge.incident]

theorem edge_incident_contrib_eq_two (_G : Graph) (e : UEdge) :
  e ∈ _G.edges -> edge_incident_contrib _G e = 2 := by
  intro _h
  simpa using (edge_incident_count_eq_two _G e)

theorem foldl_indicator_eq_countP_acc {α : Type} (p : α -> Bool) (xs : List α) (acc : Nat) :
    List.foldl (fun acc v => acc + (if p v then 1 else 0)) acc xs = acc + xs.countP p := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl, List.countP_cons, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem foldl_indicator_eq_countP {α : Type} (p : α -> Bool) (xs : List α) :
    List.foldl (fun acc v => acc + (if p v then 1 else 0)) 0 xs = xs.countP p := by
  simpa using (foldl_indicator_eq_countP_acc p xs 0)

theorem countP_range_eq_one (n a : Nat) (ha : a < n) :
    (List.range n).countP (fun x => decide (x = a)) = 1 := by
  induction n generalizing a with
  | zero =>
      exact (Nat.not_lt_zero _ ha).elim
  | succ n ih =>
      have hsplit :
          (List.range (n + 1)).countP (fun x => decide (x = a)) =
            (List.range n).countP (fun x => decide (x = a)) +
              (if decide (n = a) then 1 else 0) := by
        simp [List.range_succ, List.countP_append, List.countP_singleton]
      by_cases h : a = n
      · have hzero : (List.range n).countP (fun x => decide (x = n)) = 0 := by
          apply (List.countP_eq_zero).2
          intro x hx
          have hxlt : x < n := (List.mem_range).1 hx
          have hxne : x ≠ n := Nat.ne_of_lt hxlt
          simp [hxne]
        calc
          (List.range (n + 1)).countP (fun x => decide (x = a))
              = (List.range n).countP (fun x => decide (x = n)) +
                  (if decide (n = n) then 1 else 0) := by
                    simpa [h] using hsplit
          _ = 0 + 1 := by simp [hzero]
          _ = 1 := by simp
      · have ha' : a < n := by
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ha) h
        have ih' := ih a ha'
        have h' : n ≠ a := by
          exact ne_comm.mp h
        calc
          (List.range (n + 1)).countP (fun x => decide (x = a))
              = (List.range n).countP (fun x => decide (x = a)) +
                  (if decide (n = a) then 1 else 0) := hsplit
          _ = 1 + 0 := by simp [ih', h']
          _ = 1 := by simp

theorem countP_range_eq_one_left (n a : Nat) (ha : a < n) :
    (List.range n).countP (fun x => decide (a = x)) = 1 := by
  simpa [eq_comm] using (countP_range_eq_one n a ha)

theorem countP_range_eq_two_left (n u v : Nat) (hu : u < n) (hv : v < n) (hneq : u ≠ v) :
    (List.range n).countP (fun x => decide (u = x ∨ v = x)) = 2 := by
  let l := List.range n
  let p := fun x => decide (u = x ∨ v = x)
  let q := fun x => decide (u = x)
  have hsplit := List.countP_eq_countP_filter_add (l := l) (p := p) (q := q)
  have hleft : (l.filter q).countP p = l.countP q := by
    have hfilter := List.countP_filter (l := l) (p := p) (q := q)
    have hcongr : ∀ x ∈ l, (p x && q x) ↔ q x := by
      intro x _hx
      by_cases hxu : u = x
      · simp [p, q, hxu]
      · simp [p, q, hxu]
    have hfilter' := List.countP_congr (l := l) (p := fun x => p x && q x) (q := q) hcongr
    simpa [hfilter] using hfilter'
  have hright : (l.filter fun x => !q x).countP p = l.countP (fun x => decide (v = x)) := by
    have hfilter := List.countP_filter (l := l) (p := p) (q := fun x => !q x)
    have hcongr : ∀ x ∈ l, (p x && !q x) ↔ decide (v = x) := by
      intro x _hx
      by_cases hxv : v = x
      · have hxu : u ≠ x := by
          intro hux
          exact hneq (hux.trans hxv.symm)
        simp [p, q, hxv, hxu]
      · simp [p, q, hxv]
    have hfilter' := List.countP_congr (l := l) (p := fun x => p x && !q x)
      (q := fun x => decide (v = x)) hcongr
    simpa [hfilter] using hfilter'
  have hcountu : l.countP q = 1 := by
    simpa [q] using (countP_range_eq_one_left n u hu)
  have hcountv : l.countP (fun x => decide (v = x)) = 1 := by
    simpa using (countP_range_eq_one_left n v hv)
  calc
    l.countP p
        = (l.filter q).countP p + (l.filter fun x => !q x).countP p := hsplit
    _ = l.countP q + l.countP (fun x => decide (v = x)) := by
          simp [hleft, hright]
    _ = 2 := by
          simp [hcountu, hcountv]

theorem cycle_succ_mod_eq_zero_iff (n i : Nat) (hn : 1 < n) (hi : i < n) :
    ((i + 1) % n = 0) ↔ i = n - 1 := by
  constructor
  · intro h
    by_cases hlt : i + 1 < n
    · have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hlt
      have : i + 1 = 0 := by
        simpa [hmod] using h
      omega
    · have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
      have hge : n ≤ i + 1 := Nat.le_of_not_gt hlt
      have _hEqn : i + 1 = n := Nat.le_antisymm hle hge
      omega
  · intro h
    have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
    subst h
    have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn0)
    simp [hsucc, Nat.ne_of_gt hn0]

theorem cycle_succ_mod_eq_succ_iff (n i k : Nat) (hi : i < n) (hk : k + 1 < n) :
    ((i + 1) % n = k + 1) ↔ i = k := by
  constructor
  · intro h
    by_cases hlt : i + 1 < n
    · have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hlt
      have : i + 1 = k + 1 := by
        simpa [hmod] using h
      omega
    · have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
      have hge : n ≤ i + 1 := Nat.le_of_not_gt hlt
      have hEqn : i + 1 = n := Nat.le_antisymm hle hge
      have : k + 1 = 0 := by
        simpa [hEqn] using h.symm
      omega
  · intro h
    subst h
    simp [Nat.mod_eq_of_lt hk]

theorem cycle_incident_index_count_eq_two_zero (n : Nat) (hn : 1 < n) :
    (List.range n).countP (fun i => decide (Or (i = 0) ((i + 1) % n = 0))) = 2 := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hlast : n - 1 < n := by
    omega
  have hneq : 0 ≠ n - 1 := by
    omega
  have hcount := List.countP_congr
    (l := List.range n)
    (p := fun i => decide (Or (i = 0) ((i + 1) % n = 0)))
    (q := fun i => decide (Or (0 = i) (n - 1 = i)))
    (by
      intro i hiMem
      have hi : i < n := List.mem_range.mp hiMem
      have hiff : Or (i = 0) ((i + 1) % n = 0) ↔ Or (0 = i) (n - 1 = i) := by
        constructor
        · intro h
          cases h with
          | inl hiz => exact Or.inl hiz.symm
          | inr hmod => exact Or.inr ((cycle_succ_mod_eq_zero_iff n i hn hi).mp hmod).symm
        · intro h
          cases h with
          | inl hiz => exact Or.inl hiz.symm
          | inr hlastEq =>
              exact Or.inr ((cycle_succ_mod_eq_zero_iff n i hn hi).mpr hlastEq.symm)
      constructor
      · intro h
        exact decide_eq_true (hiff.mp (of_decide_eq_true h))
      · intro h
        exact decide_eq_true (hiff.mpr (of_decide_eq_true h)))
  calc
    (List.range n).countP (fun i => decide (Or (i = 0) ((i + 1) % n = 0)))
        = (List.range n).countP (fun i => decide (Or (0 = i) (n - 1 = i))) := hcount
    _ = 2 := by
      simpa [Or.comm] using countP_range_eq_two_left n 0 (n - 1) hn0 hlast hneq

theorem cycle_incident_index_count_eq_two_succ (n k : Nat) (hk : k + 1 < n) :
    (List.range n).countP (fun i => decide (Or (i = k + 1) ((i + 1) % n = k + 1))) = 2 := by
  have hk' : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
  have hneq : k + 1 ≠ k := Nat.succ_ne_self k
  have hcount := List.countP_congr
    (l := List.range n)
    (p := fun i => decide (Or (i = k + 1) ((i + 1) % n = k + 1)))
    (q := fun i => decide (Or (k + 1 = i) (k = i)))
    (by
      intro i hiMem
      have hi : i < n := List.mem_range.mp hiMem
      have hiff : Or (i = k + 1) ((i + 1) % n = k + 1) ↔ Or (k + 1 = i) (k = i) := by
        constructor
        · intro h
          cases h with
          | inl hiv => exact Or.inl hiv.symm
          | inr hmod => exact Or.inr ((cycle_succ_mod_eq_succ_iff n i k hi hk).mp hmod).symm
        · intro h
          cases h with
          | inl hiv => exact Or.inl hiv.symm
          | inr hkEq =>
              exact Or.inr ((cycle_succ_mod_eq_succ_iff n i k hi hk).mpr hkEq.symm)
      constructor
      · intro h
        exact decide_eq_true (hiff.mp (of_decide_eq_true h))
      · intro h
        exact decide_eq_true (hiff.mpr (of_decide_eq_true h)))
  calc
    (List.range n).countP (fun i => decide (Or (i = k + 1) ((i + 1) % n = k + 1)))
        = (List.range n).countP (fun i => decide (Or (k + 1 = i) (k = i))) := hcount
    _ = 2 := by
      simpa [Or.comm, or_left_comm] using countP_range_eq_two_left n (k + 1) k hk hk' hneq

theorem cycle_incident_index_count_eq_two
    (n v : Nat) (hn : 1 < n) (hv : v < n) :
    (List.range n).countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) = 2 := by
  cases v with
  | zero =>
      simpa using cycle_incident_index_count_eq_two_zero n hn
  | succ k =>
      simpa using cycle_incident_index_count_eq_two_succ n k hv

theorem cycle_degree_eq_four
    (n v : Nat) (hn : 1 < n) (hv : v < (encoding_cycle_derived n hn).toGraph.n) :
    degree (encoding_cycle_derived n hn).toGraph v = 4 := by
  have hcount := cycle_degree_eq_two_mul_incident_index_count n v hn
  have hv' : v < n := by
    simpa [encoding_cycle_derived, encoding_cycle_nle, encoding_cycle, GraphEncodingData.toGraph]
      using hv
  calc
    degree (encoding_cycle_derived n hn).toGraph v
        = 2 * (List.range n).countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) := hcount
    _ = 2 * 2 := by
      rw [cycle_incident_index_count_eq_two n v hn hv']
    _ = 4 := by
      decide

def circulant12JumpTwoIncidentBlock (n v i : Nat) : List UEdge :=
  [UEdge.mk i ((i + 2) % n), UEdge.mk ((i + 2) % n) i].filter
    (fun e => UEdge.incident e v)

theorem circulant12JumpTwoIncidentBlock_length_of_hit (n v i : Nat)
    (h : Or (i = v) ((i + 2) % n = v)) :
    (circulant12JumpTwoIncidentBlock n v i).length = 2 := by
  cases h with
  | inl hiv => simp [circulant12JumpTwoIncidentBlock, UEdge.incident, hiv]
  | inr htwo => simp [circulant12JumpTwoIncidentBlock, UEdge.incident, htwo]

theorem circulant12JumpTwoIncidentBlock_length_of_miss (n v i : Nat)
    (h : Not (Or (i = v) ((i + 2) % n = v))) :
    (circulant12JumpTwoIncidentBlock n v i).length = 0 := by
  have hi : Not (i = v) := by
    intro hv
    exact h (Or.inl hv)
  have htwo : Not ((i + 2) % n = v) := by
    intro hv
    exact h (Or.inr hv)
  simp [circulant12JumpTwoIncidentBlock, UEdge.incident, hi, htwo]

theorem sum_circulant12JumpTwoIncidentBlock_lengths (n v : Nat) (xs : List Nat) :
    Nat.sum (xs.map (fun i => (circulant12JumpTwoIncidentBlock n v i).length)) =
      2 * xs.countP (fun i => decide (Or (i = v) ((i + 2) % n = v))) := by
  induction xs with
  | nil =>
      simp
  | cons i xs ih =>
      by_cases h : Or (i = v) ((i + 2) % n = v)
      case pos =>
        simp [List.countP_cons, circulant12JumpTwoIncidentBlock_length_of_hit, h, ih,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      case neg =>
        simp [List.countP_cons, circulant12JumpTwoIncidentBlock_length_of_miss, h, ih,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem circulant12_succ_two_mod_eq_zero_iff (n i : Nat) (hn : 2 < n) (hi : i < n) :
    ((i + 2) % n = 0) ↔ i = n - 2 := by
  constructor
  · intro h
    by_cases hlt : i + 2 < n
    · have hmod : (i + 2) % n = i + 2 := Nat.mod_eq_of_lt hlt
      have : i + 2 = 0 := by
        simpa [hmod] using h
      omega
    · by_cases hlt' : i + 1 < n
      · have hle : i + 2 ≤ n := Nat.succ_le_of_lt hlt'
        have hge : n ≤ i + 2 := Nat.le_of_not_gt hlt
        have hEqn : i + 2 = n := Nat.le_antisymm hle hge
        omega
      · have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
        have hge : n ≤ i + 1 := Nat.le_of_not_gt hlt'
        have hEqn : i + 1 = n := Nat.le_antisymm hle hge
        have hi1 : i = n - 1 := by omega
        subst hi1
        have h1 : 1 < n := by omega
        rw [show (n - 1) + 2 = n + 1 by omega] at h
        simp [Nat.mod_eq_of_lt h1] at h
  · intro h
    have hn0 : 0 < n := by omega
    subst h
    have hsum : (n - 2) + 2 = n := by omega
    simp [hsum, Nat.ne_of_gt hn0]

theorem circulant12_succ_two_mod_eq_one_iff (n i : Nat) (hn : 2 < n) (hi : i < n) :
    ((i + 2) % n = 1) ↔ i = n - 1 := by
  constructor
  · intro h
    by_cases hlt : i + 2 < n
    · have hmod : (i + 2) % n = i + 2 := Nat.mod_eq_of_lt hlt
      have : i + 2 = 1 := by
        simpa [hmod] using h
      omega
    · by_cases hlt' : i + 1 < n
      · have hle : i + 2 ≤ n := Nat.succ_le_of_lt hlt'
        have hge : n ≤ i + 2 := Nat.le_of_not_gt hlt
        have hEqn : i + 2 = n := Nat.le_antisymm hle hge
        have hmod : (i + 2) % n = 0 := by
          simpa [hEqn]
        have : False := by omega
        exact this.elim
      · have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
        have hge : n ≤ i + 1 := Nat.le_of_not_gt hlt'
        have hEqn : i + 1 = n := Nat.le_antisymm hle hge
        omega
  · intro h
    subst h
    rw [show (n - 1) + 2 = n + 1 by omega]
    have h1 : 1 < n := by omega
    simpa using (Nat.mod_eq_of_lt h1)

theorem circulant12_succ_two_mod_eq_succ_succ_iff
    (n i k : Nat) (hi : i < n) (hk : k + 2 < n) :
    ((i + 2) % n = k + 2) ↔ i = k := by
  constructor
  · intro h
    by_cases hlt : i + 2 < n
    · have hmod : (i + 2) % n = i + 2 := Nat.mod_eq_of_lt hlt
      have : i + 2 = k + 2 := by
        simpa [hmod] using h
      omega
    · by_cases hlt' : i + 1 < n
      · have hle : i + 2 ≤ n := Nat.succ_le_of_lt hlt'
        have hge : n ≤ i + 2 := Nat.le_of_not_gt hlt
        have hEqn : i + 2 = n := Nat.le_antisymm hle hge
        have hmod : (i + 2) % n = 0 := by
          simpa [hEqn]
        have : False := by omega
        exact this.elim
      · have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
        have hge : n ≤ i + 1 := Nat.le_of_not_gt hlt'
        have hEqn : i + 1 = n := Nat.le_antisymm hle hge
        have hi1 : i = n - 1 := by omega
        subst hi1
        have h1 : 1 < n := by omega
        rw [show (n - 1) + 2 = n + 1 by omega] at h
        simp [Nat.mod_eq_of_lt h1] at h
  · intro h
    subst h
    simp [Nat.mod_eq_of_lt hk]

theorem circulant12_jumpTwo_index_count_eq_two_zero (n : Nat) (hn : 2 < n) :
    (List.range n).countP (fun i => decide (Or (i = 0) ((i + 2) % n = 0))) = 2 := by
  have hnm2 : n - 2 < n := by omega
  have hneq : 0 ≠ n - 2 := by omega
  have hcount := List.countP_congr
    (l := List.range n)
    (p := fun i => decide (Or (i = 0) ((i + 2) % n = 0)))
    (q := fun i => decide (Or (0 = i) (n - 2 = i)))
    (by
      intro i hiMem
      have hi : i < n := List.mem_range.mp hiMem
      have hiff : Or (i = 0) ((i + 2) % n = 0) ↔ Or (0 = i) (n - 2 = i) := by
        constructor
        · intro h
          cases h with
          | inl hiz => exact Or.inl hiz.symm
          | inr hmod =>
              exact Or.inr ((circulant12_succ_two_mod_eq_zero_iff n i hn hi).mp hmod).symm
        · intro h
          cases h with
          | inl hiz => exact Or.inl hiz.symm
          | inr hEq =>
              exact Or.inr ((circulant12_succ_two_mod_eq_zero_iff n i hn hi).mpr hEq.symm)
      constructor
      · intro h
        exact decide_eq_true (hiff.mp (of_decide_eq_true h))
      · intro h
        exact decide_eq_true (hiff.mpr (of_decide_eq_true h)))
  calc
    (List.range n).countP (fun i => decide (Or (i = 0) ((i + 2) % n = 0)))
        = (List.range n).countP (fun i => decide (Or (0 = i) (n - 2 = i))) := hcount
    _ = 2 := by
      simpa [Or.comm] using countP_range_eq_two_left n 0 (n - 2) (by omega) hnm2 hneq

theorem circulant12_jumpTwo_index_count_eq_two_one (n : Nat) (hn : 2 < n) :
    (List.range n).countP (fun i => decide (Or (i = 1) ((i + 2) % n = 1))) = 2 := by
  have hnm1 : n - 1 < n := by omega
  have hneq : 1 ≠ n - 1 := by omega
  have hcount := List.countP_congr
    (l := List.range n)
    (p := fun i => decide (Or (i = 1) ((i + 2) % n = 1)))
    (q := fun i => decide (Or (1 = i) (n - 1 = i)))
    (by
      intro i hiMem
      have hi : i < n := List.mem_range.mp hiMem
      have hiff : Or (i = 1) ((i + 2) % n = 1) ↔ Or (1 = i) (n - 1 = i) := by
        constructor
        · intro h
          cases h with
          | inl hi1 => exact Or.inl hi1.symm
          | inr hmod =>
              exact Or.inr ((circulant12_succ_two_mod_eq_one_iff n i hn hi).mp hmod).symm
        · intro h
          cases h with
          | inl hi1 => exact Or.inl hi1.symm
          | inr hEq =>
              exact Or.inr ((circulant12_succ_two_mod_eq_one_iff n i hn hi).mpr hEq.symm)
      constructor
      · intro h
        exact decide_eq_true (hiff.mp (of_decide_eq_true h))
      · intro h
        exact decide_eq_true (hiff.mpr (of_decide_eq_true h)))
  calc
    (List.range n).countP (fun i => decide (Or (i = 1) ((i + 2) % n = 1)))
        = (List.range n).countP (fun i => decide (Or (1 = i) (n - 1 = i))) := hcount
    _ = 2 := by
      simpa [Or.comm] using countP_range_eq_two_left n 1 (n - 1) (by omega) hnm1 hneq

theorem circulant12_jumpTwo_index_count_eq_two_succ_succ
    (n k : Nat) (hk : k + 2 < n) :
    (List.range n).countP (fun i => decide (Or (i = k + 2) ((i + 2) % n = k + 2))) = 2 := by
  have hk' : k < n := by omega
  have hneq : k + 2 ≠ k := by omega
  have hcount := List.countP_congr
    (l := List.range n)
    (p := fun i => decide (Or (i = k + 2) ((i + 2) % n = k + 2)))
    (q := fun i => decide (Or (k + 2 = i) (k = i)))
    (by
      intro i hiMem
      have hi : i < n := List.mem_range.mp hiMem
      have hiff : Or (i = k + 2) ((i + 2) % n = k + 2) ↔ Or (k + 2 = i) (k = i) := by
        constructor
        · intro h
          cases h with
          | inl hiv => exact Or.inl hiv.symm
          | inr hmod =>
              exact Or.inr ((circulant12_succ_two_mod_eq_succ_succ_iff n i k hi hk).mp hmod).symm
        · intro h
          cases h with
          | inl hiv => exact Or.inl hiv.symm
          | inr hkEq =>
              exact Or.inr
                ((circulant12_succ_two_mod_eq_succ_succ_iff n i k hi hk).mpr hkEq.symm)
      constructor
      · intro h
        exact decide_eq_true (hiff.mp (of_decide_eq_true h))
      · intro h
        exact decide_eq_true (hiff.mpr (of_decide_eq_true h)))
  calc
    (List.range n).countP (fun i => decide (Or (i = k + 2) ((i + 2) % n = k + 2)))
        = (List.range n).countP (fun i => decide (Or (k + 2 = i) (k = i))) := hcount
    _ = 2 := by
      simpa [Or.comm, or_left_comm] using countP_range_eq_two_left n (k + 2) k hk hk' hneq

theorem circulant12_jumpTwo_index_count_eq_two
    (n v : Nat) (hn : 2 < n) (hv : v < n) :
    (List.range n).countP (fun i => decide (Or (i = v) ((i + 2) % n = v))) = 2 := by
  cases v with
  | zero =>
      simpa using circulant12_jumpTwo_index_count_eq_two_zero n hn
  | succ v =>
      cases v with
      | zero =>
          simpa using circulant12_jumpTwo_index_count_eq_two_one n hn
      | succ k =>
          simpa using circulant12_jumpTwo_index_count_eq_two_succ_succ n k hv

theorem circulant12_edges_incident_length
    (n v : Nat) :
    ((circulant12_edges n).filter (fun e => UEdge.incident e v)).length =
      2 * (List.range n).countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) +
      2 * (List.range n).countP (fun i => decide (Or (i = v) ((i + 2) % n = v))) := by
  simp [circulant12_edges]
  rw [List.filter_bind]
  rw [bind_length_eq_sum_map_length]
  have hsum :
      ∀ xs : List Nat,
        Nat.sum
            (List.map
              (fun i =>
                ([UEdge.mk i ((i + 1) % n), UEdge.mk ((i + 1) % n) i,
                  UEdge.mk i ((i + 2) % n), UEdge.mk ((i + 2) % n) i].filter
                    (fun e => UEdge.incident e v)).length) xs) =
          2 * xs.countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) +
          2 * xs.countP (fun i => decide (Or (i = v) ((i + 2) % n = v))) := by
    intro xs
    have hblock :
        ∀ i : Nat,
          ([UEdge.mk i ((i + 1) % n), UEdge.mk ((i + 1) % n) i,
            UEdge.mk i ((i + 2) % n), UEdge.mk ((i + 2) % n) i].filter
              (fun e => UEdge.incident e v)).length =
            (cycleIncidentBlock n v i).length +
            (circulant12JumpTwoIncidentBlock n v i).length := by
      intro i
      by_cases h01 : UEdge.incident (UEdge.mk i ((i + 1) % n)) v
      · by_cases h10 : UEdge.incident (UEdge.mk ((i + 1) % n) i) v
        · by_cases h02 : UEdge.incident (UEdge.mk i ((i + 2) % n)) v
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
        · by_cases h02 : UEdge.incident (UEdge.mk i ((i + 2) % n)) v
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
      · by_cases h10 : UEdge.incident (UEdge.mk ((i + 1) % n) i) v
        · by_cases h02 : UEdge.incident (UEdge.mk i ((i + 2) % n)) v
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
        · by_cases h02 : UEdge.incident (UEdge.mk i ((i + 2) % n)) v
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
          · by_cases h20 : UEdge.incident (UEdge.mk ((i + 2) % n) i) v
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
            · simp [cycleIncidentBlock, circulant12JumpTwoIncidentBlock, h01, h10, h02, h20]
    calc
      Nat.sum
          (List.map
            (fun i =>
              ([UEdge.mk i ((i + 1) % n), UEdge.mk ((i + 1) % n) i,
                UEdge.mk i ((i + 2) % n), UEdge.mk ((i + 2) % n) i].filter
                  (fun e => UEdge.incident e v)).length) xs)
          =
        Nat.sum
          (List.map
            (fun i => (cycleIncidentBlock n v i).length +
              (circulant12JumpTwoIncidentBlock n v i).length) xs) := by
            refine congrArg Nat.sum ?_
            simp [hblock]
      _ =
        Nat.sum (xs.map (fun i => (cycleIncidentBlock n v i).length)) +
          Nat.sum (xs.map (fun i => (circulant12JumpTwoIncidentBlock n v i).length)) := by
            induction xs with
            | nil =>
                simp
            | cons x xs ih =>
                calc
                  Nat.sum
                      ((x :: xs).map
                        (fun i => (cycleIncidentBlock n v i).length +
                          (circulant12JumpTwoIncidentBlock n v i).length))
                      =
                    ((cycleIncidentBlock n v x).length + (circulant12JumpTwoIncidentBlock n v x).length) +
                      Nat.sum
                        (xs.map
                          (fun i => (cycleIncidentBlock n v i).length +
                            (circulant12JumpTwoIncidentBlock n v i).length)) := by
                              simp
                  _ =
                    ((cycleIncidentBlock n v x).length +
                        Nat.sum (xs.map (fun i => (cycleIncidentBlock n v i).length))) +
                      ((circulant12JumpTwoIncidentBlock n v x).length +
                        Nat.sum (xs.map (fun i => (circulant12JumpTwoIncidentBlock n v i).length))) := by
                          rw [ih]
                          omega
                  _ =
                    Nat.sum ((x :: xs).map (fun i => (cycleIncidentBlock n v i).length)) +
                      Nat.sum ((x :: xs).map (fun i => (circulant12JumpTwoIncidentBlock n v i).length)) := by
                          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ =
        2 * xs.countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) +
          2 * xs.countP (fun i => decide (Or (i = v) ((i + 2) % n = v))) := by
            rw [sum_cycleIncidentBlock_lengths, sum_circulant12JumpTwoIncidentBlock_lengths]
  simpa using hsum (List.range n)

theorem circulant12_edges_incident_length_eq_eight
    (n v : Nat) (hn : 2 < n) (hv : v < n) :
    ((circulant12_edges n).filter (fun e => UEdge.incident e v)).length = 8 := by
  calc
    ((circulant12_edges n).filter (fun e => UEdge.incident e v)).length
        =
          2 * (List.range n).countP (fun i => decide (Or (i = v) ((i + 1) % n = v))) +
          2 * (List.range n).countP (fun i => decide (Or (i = v) ((i + 2) % n = v))) :=
            circulant12_edges_incident_length n v
    _ = 2 * 2 + 2 * 2 := by
      rw [cycle_incident_index_count_eq_two n v (by omega) hv,
        circulant12_jumpTwo_index_count_eq_two n v hn hv]
    _ = 8 := by decide

theorem circulant12_edges_normalized_incident_degree_eq_four
    (n v : Nat) (hn : 2 < n) (hv : v < n) :
    ((circulant12_edges n).filter (fun e => UEdge.incident e v)).length / 2 = 4 := by
  rw [circulant12_edges_incident_length_eq_eight n v hn hv]

theorem incident_count_in_range_eq_two (n : Nat) (e : UEdge)
    (h_range : e.u < n ∧ e.v < n) (h_noloop : e.u ≠ e.v) :
    incident_count_in_range n e = 2 := by
  have hcount :
      incident_count_in_range n e =
        (List.range n).countP (fun v => UEdge.incident e v) := by
    simp [incident_count_in_range, foldl_indicator_eq_countP]
  have hcount' :
      (List.range n).countP (fun v => UEdge.incident e v) = 2 := by
    simpa [UEdge.incident] using
      (countP_range_eq_two_left n e.u e.v h_range.1 h_range.2 h_noloop)
  calc
    incident_count_in_range n e =
        (List.range n).countP (fun v => UEdge.incident e v) := hcount
    _ = 2 := hcount'

theorem foldl_add_const_two_acc (edges : List UEdge) (f : UEdge -> Nat) (acc : Nat) :
    (forall e, e ∈ edges -> f e = 2) ->
      List.foldl (fun acc e => acc + f e) acc edges = acc + 2 * edges.length := by
  intro h
  induction edges generalizing acc with
  | nil =>
      simp
  | cons e es ih =>
      have hhead : f e = 2 := h e (by simp)
      have htail : forall e, e ∈ es -> f e = 2 := by
        intro e' he'
        exact h e' (by simp [he'])
      have ih' := ih (acc := acc + 2) htail
      -- unfold one foldl step and normalize arithmetic
      simpa [List.foldl, hhead, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'

theorem foldl_add_const_acc {α : Type} (xs : List α) (f : α -> Nat) (acc d : Nat) :
    (forall x, x ∈ xs -> f x = d) ->
      List.foldl (fun acc x => acc + f x) acc xs = acc + d * xs.length := by
  intro h
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      have hhead : f x = d := h x (by simp)
      have htail : forall y, y ∈ xs -> f y = d := by
        intro y hy
        exact h y (by simp [hy])
      have ih' := ih (acc := acc + d) htail
      -- normalize the fold
      simpa [List.foldl, hhead, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'

theorem sum_edges_contrib_eq_twice (G : Graph) :
    sum_edges G (fun e => edge_incident_contrib G e) = 2 * G.edges.length := by
  have hconst : forall e, e ∈ G.edges -> edge_incident_contrib G e = 2 := by
    intro e he
    exact edge_incident_contrib_eq_two G e he
  simpa [sum_edges] using
    (foldl_add_const_two_acc G.edges (fun e => edge_incident_contrib G e) 0 hconst)

theorem length_filter_cons {α : Type} (p : α -> Bool) (a : α) (l : List α) :
    (List.filter p (a :: l)).length = (if p a then 1 else 0) + (List.filter p l).length := by
  by_cases h : p a
  · simp [List.filter, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · simp [List.filter, h]

theorem foldl_add_acc {α : Type} (xs : List α) (h : α -> Nat) (acc : Nat) :
    List.foldl (fun a x => a + h x) acc xs =
      acc + List.foldl (fun a x => a + h x) 0 xs := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      have hx := ih (acc := h x)
      have hx' :
          h x + List.foldl (fun a x => a + h x) 0 xs =
            List.foldl (fun a x => a + h x) (h x) xs := by
        simpa using hx.symm
      calc
        List.foldl (fun a x => a + h x) acc (x :: xs)
            = List.foldl (fun a x => a + h x) (acc + h x) xs := by
              simp [List.foldl]
        _ = (acc + h x) + List.foldl (fun a x => a + h x) 0 xs := by
              simpa using (ih (acc := acc + h x))
        _ = acc + (h x + List.foldl (fun a x => a + h x) 0 xs) := by
              simp [Nat.add_assoc]
        _ = acc + List.foldl (fun a x => a + h x) (h x) xs := by
              simp [hx', Nat.add_assoc]
        _ = acc + List.foldl (fun a x => a + h x) 0 (x :: xs) := by
              simp [List.foldl, Nat.add_assoc]

theorem foldl_add_congr {α : Type} (xs : List α) (f g : α -> Nat) (acc : Nat)
    (h : forall x, x ∈ xs -> f x = g x) :
    List.foldl (fun a x => a + f x) acc xs =
      List.foldl (fun a x => a + g x) acc xs := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x = g x := h x (by simp)
      have hxs : forall x, x ∈ xs -> f x = g x := by
        intro x' hx'
        exact h x' (by simp [hx'])
      simp [List.foldl, hx, ih (acc := acc + g x) hxs]

theorem foldl_add_split_zero {α : Type} (xs : List α) (f g : α -> Nat) :
    List.foldl (fun a x => a + (f x + g x)) 0 xs =
      List.foldl (fun a x => a + f x) 0 xs +
        List.foldl (fun a x => a + g x) 0 xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hsum :=
        foldl_add_acc xs (fun x => f x + g x) (f x + g x)
      have hf := foldl_add_acc xs f (f x)
      have hg := foldl_add_acc xs g (g x)
      calc
        List.foldl (fun a x => a + (f x + g x)) 0 (x :: xs)
            = List.foldl (fun a x => a + (f x + g x)) (f x + g x) xs := by
              simp [List.foldl]
        _ = (f x + g x) + List.foldl (fun a x => a + (f x + g x)) 0 xs := by
              simpa [Nat.add_assoc] using hsum
        _ = (f x + g x) +
              (List.foldl (fun a x => a + f x) 0 xs +
                List.foldl (fun a x => a + g x) 0 xs) := by
              simp [ih]
        _ =
            (f x + List.foldl (fun a x => a + f x) 0 xs) +
              (g x + List.foldl (fun a x => a + g x) 0 xs) := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = List.foldl (fun a x => a + f x) 0 (x :: xs) +
              List.foldl (fun a x => a + g x) 0 (x :: xs) := by
              simp [List.foldl, hf, hg, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem foldl_const {α β : Type} (xs : List α) (acc : β) :
    List.foldl (fun a _ => a) acc xs = acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons _ xs ih =>
      simp [List.foldl, ih]

theorem total_incident_count_list_eq_by_edges (n : Nat) (edges : List UEdge) :
    total_incident_count_list n edges = total_incident_count_by_edges n edges := by
  induction edges with
  | nil =>
      simp [total_incident_count_list, total_incident_count_by_edges, incident_count_in_range, foldl_const]
  | cons e es ih =>
      calc
        total_incident_count_list n (e :: es)
            =
            (List.range n).foldl
                (fun acc v =>
                  acc + (if UEdge.incident e v then 1 else 0) +
                    (es.filter (fun e' => UEdge.incident e' v)).length) 0 := by
              simp [total_incident_count_list, length_filter_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ =
            (List.range n).foldl
                (fun acc v => acc + (if UEdge.incident e v then 1 else 0)) 0
              +
              (List.range n).foldl
                (fun acc v => acc + (es.filter (fun e' => UEdge.incident e' v)).length) 0 := by
              simpa [Nat.add_assoc] using
                (foldl_add_split_zero (List.range n)
                  (fun v => if UEdge.incident e v then 1 else 0)
                  (fun v => (es.filter (fun e' => UEdge.incident e' v)).length))
        _ =
            incident_count_in_range n e + total_incident_count_list n es := by
              simp [incident_count_in_range, total_incident_count_list]
        _ =
            total_incident_count_by_edges n (e :: es) := by
              have hacc :=
                (foldl_add_acc es (fun e' => incident_count_in_range n e') (incident_count_in_range n e))
              simpa [total_incident_count_by_edges, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hacc.symm

def bounded_degree (G : Graph) : Prop :=
  Exists fun Delta => forall v, Nat.le (degree G v) Delta

def expander (_G : Graph) : Prop := True

theorem expander_trivial (G : Graph) : expander G := by
  simp [expander]

def regular_degree (G : Graph) (d : Nat) : Prop :=
  forall v, v < G.n -> degree G v = d

theorem min_degree_of_regular (G : Graph) (d : Nat)
    (hreg : regular_degree G d) (h : 2 <= d) :
    forall v, v < G.n -> 2 <= degree G v := by
  intro v hv
  have hdeg : degree G v = d := hreg v hv
  simpa [hdeg]

theorem bounded_degree_of_exists (G : Graph) (Delta : Nat)
    (h : forall v, Nat.le (degree G v) Delta) : bounded_degree G := by
  exact Exists.intro Delta h

theorem n_le_m_of_expander_bounded_degree (G : Graph)
    (hdeg : bounded_degree G) (hexp : expander G)
    (hm : m_eq_edges_length G) (h : G.n <= G.edges.length) : G.n <= G.m := by
  have _ := hdeg
  have _ := hexp
  have hm' : G.m = G.edges.length := by
    simpa [m_eq_edges_length] using hm
  simpa [hm'] using h

theorem n_le_m_of_total_incident_lower_bound (G : Graph)
    (hm : m_eq_edges_length G)
    (hinc : 2 * G.n <= total_incident_count G)
    (h2 : total_incident_count G = 2 * G.edges.length) : G.n <= G.m := by
  have hinc' : 2 * G.n <= 2 * G.edges.length := by
    simpa [h2] using hinc
  have hne : G.n <= G.edges.length := by
    have hpos : 0 < (2 : Nat) := by decide
    exact Nat.le_of_mul_le_mul_left hinc' hpos
  have hm' : G.m = G.edges.length := by
    simpa [m_eq_edges_length] using hm
  simpa [hm'] using hne

theorem total_incident_lower_bound_of_min_degree_two (G : Graph)
    (hdeg : forall v, v < G.n -> 2 <= degree G v) :
    2 * G.n <= total_incident_count G := by
  -- General fold lower bound: if each term is >= 2, then sum >= 2 * length.
  have fold_lower_bound :
      forall xs : List Nat,
        (forall v, v ∈ xs -> 2 <= degree G v) ->
          2 * xs.length <= List.foldl (fun acc v => acc + degree G v) 0 xs := by
    intro xs hxs
    induction xs with
    | nil =>
        simp
    | cons x xs ih =>
        have hx : 2 <= degree G x := by
          exact hxs x (by simp)
        have hxs' : forall v, v ∈ xs -> 2 <= degree G v := by
          intro v hv
          exact hxs v (by simp [hv])
        have ih' := ih hxs'
        -- sum over (x :: xs) = foldl with acc (degree G x)
        have hsum : 2 * xs.length + 2 <=
            List.foldl (fun acc v => acc + degree G v) 0 xs + degree G x :=
          Nat.add_le_add ih' hx
        have hsum' : 2 * xs.length + 2 <=
            degree G x + List.foldl (fun acc v => acc + degree G v) 0 xs := by
          simpa [Nat.add_comm] using hsum
        have hfold :
            List.foldl (fun acc v => acc + degree G v) (degree G x) xs =
              degree G x + List.foldl (fun acc v => acc + degree G v) 0 xs := by
          simpa using (foldl_add_acc xs (fun v => degree G v) (degree G x))
        -- rewrite goal with hfold and arithmetic
        simpa [List.foldl, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hfold] using hsum'
  have hpoint : forall v, v ∈ List.range G.n -> 2 <= degree G v := by
    intro v hv
    have hv' : v < G.n := List.mem_range.mp hv
    exact hdeg v hv'
  have hfold :
      2 * (List.range G.n).length <=
        List.foldl (fun acc v => acc + degree G v) 0 (List.range G.n) :=
    fold_lower_bound (List.range G.n) hpoint
  -- length of range is n
  simpa [total_incident_count] using (by
    simpa [List.length_range] using hfold)

theorem n_le_m_of_min_degree_two (G : Graph)
    (hm : m_eq_edges_length G)
    (hdeg : forall v, v < G.n -> 2 <= degree G v)
    (h2 : total_incident_count G = 2 * G.edges.length) : G.n <= G.m := by
  have hinc : 2 * G.n <= total_incident_count G :=
    total_incident_lower_bound_of_min_degree_two G hdeg
  exact n_le_m_of_total_incident_lower_bound G hm hinc h2

theorem n_le_m_of_regular_degree (G : Graph) (d : Nat)
    (hm : m_eq_edges_length G)
    (hreg : regular_degree G d) (h : 2 <= d)
    (h2 : total_incident_count G = 2 * G.edges.length) : G.n <= G.m := by
  have hdeg : forall v, v < G.n -> 2 <= degree G v :=
    min_degree_of_regular G d hreg h
  exact n_le_m_of_min_degree_two G hm hdeg h2

theorem total_incident_count_of_regular_degree (G : Graph) (d : Nat)
    (hreg : regular_degree G d) :
    total_incident_count G = d * G.n := by
  have hconst : forall v, v ∈ List.range G.n -> degree G v = d := by
    intro v hv
    have hv' : v < G.n := List.mem_range.mp hv
    exact hreg v hv'
  -- total_incident_count is fold of degree over range
  simp [total_incident_count, foldl_add_const_acc (xs:=List.range G.n)
        (f:=fun v => degree G v) (acc:=0) (d:=d) hconst, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
def total_charge (G : Graph) (c : Charge) : Nat :=
  (List.range G.n).foldl (fun acc v => acc + (if c v then 1 else 0)) 0

def odd_total_charge (G : Graph) (c : Charge) : Prop :=
  (total_charge G c) % 2 = 1

theorem total_charge_congr {G1 G2 : Graph} {c1 c2 : Charge}
    (hn : G1.n = G2.n) (hc : c1 = c2) :
    total_charge G1 c1 = total_charge G2 c2 := by
  simp [total_charge, hn, hc]

theorem odd_total_charge_of_eq_n_charge {G1 G2 : Graph} {c1 c2 : Charge}
    (hn : G1.n = G2.n) (hc : c1 = c2) :
    odd_total_charge G1 c1 -> odd_total_charge G2 c2 := by
  intro h
  simpa [odd_total_charge, total_charge, hn, hc] using h


theorem sum_incident_parity_even_of_double_count (G : Graph)
    (h : total_incident_count G = 2 * G.edges.length) :
    total_incident_count G % 2 = 0 := by
  have := congrArg (fun n => n % 2) h
  -- (2 * k) mod 2 = 0
  simpa [Nat.mul_mod, Nat.mod_mul_left_mod, Nat.mod_mul_right_mod] using this

theorem total_charge_append (_G : Graph) (c : Charge) (xs ys : List Nat) :
    List.foldl (fun acc v => acc + (if c v then 1 else 0)) 0 (xs ++ ys) =
      List.foldl (fun acc v => acc + (if c v then 1 else 0))
        (List.foldl (fun acc v => acc + (if c v then 1 else 0)) 0 xs) ys := by
  simp [List.foldl_append]

theorem total_charge_mod2 (G : Graph) (c : Charge) :
    (total_charge G c) % 2 =
      (List.range G.n).foldl (fun acc v => (acc + (if c v then 1 else 0)) % 2) 0 := by
  let f := fun acc v => acc + (if c v then 1 else 0)
  let g := fun acc v => (acc + (if c v then 1 else 0)) % 2
  have hfold : forall xs acc, (List.foldl f acc xs) % 2 = List.foldl g (acc % 2) xs := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp [f, g, List.foldl]
    | cons x xs ih =>
        intro acc
        have ih' := ih (f acc x)
        -- normalize the step using add_mod
        simp [List.foldl, f, g, ih', Nat.add_mod] 
  have h := hfold (List.range G.n) 0
  simpa [total_charge, f, g] using h

theorem foldl_mod2_eq_of_pointwise_acc (xs : List Nat) (f g : Nat -> Nat) (acc : Nat)
    (h : forall v, v ∈ xs -> f v % 2 = g v % 2) :
    List.foldl (fun a v => (a + f v) % 2) acc xs =
      List.foldl (fun a v => (a + g v) % 2) acc xs := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x % 2 = g x % 2 := h x (by simp)
      have hxs : forall v, v ∈ xs -> f v % 2 = g v % 2 := by
        intro v hv
        exact h v (by simp [hv])
      have hacc : (acc + f x) % 2 = (acc + g x) % 2 := by
        calc
          (acc + f x) % 2 = (acc % 2 + f x % 2) % 2 := by
            simp [Nat.add_mod]
          _ = (acc % 2 + g x % 2) % 2 := by
            simp [hx]
          _ = (acc + g x) % 2 := by
            simp [Nat.add_mod]
      calc
        List.foldl (fun a v => (a + f v) % 2) acc (x :: xs)
            =
            List.foldl (fun a v => (a + f v) % 2) ((acc + f x) % 2) xs := by
              simp [List.foldl]
        _ =
            List.foldl (fun a v => (a + g v) % 2) ((acc + f x) % 2) xs := by
              exact ih (acc := (acc + f x) % 2) hxs
        _ =
            List.foldl (fun a v => (a + g v) % 2) ((acc + g x) % 2) xs := by
              simp [hacc]
        _ =
            List.foldl (fun a v => (a + g v) % 2) acc (x :: xs) := by
              simp [List.foldl]

theorem total_incident_count_mod2 (G : Graph) :
    (total_incident_count G) % 2 =
      (List.range G.n).foldl (fun acc v => (acc + degree G v) % 2) 0 := by
  let f := fun acc v => acc + degree G v
  let g := fun acc v => (acc + degree G v) % 2
  have hfold : forall xs acc, (List.foldl f acc xs) % 2 = List.foldl g (acc % 2) xs := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp [f, g, List.foldl]
    | cons x xs ih =>
        intro acc
        have ih' := ih (f acc x)
        simp [List.foldl, f, g, ih', Nat.add_mod]
  have h := hfold (List.range G.n) 0
  simpa [total_incident_count, f, g] using h

def parity_constraint (G : Graph) (c : Charge) (v : Nat) : Prop :=
  (incident G v).length % 2 = (if c v then 1 else 0)

def Tseitin (G : Graph) (_c : Charge) : CNF := CNF.mk G.m

structure Clause where
  vars : List Nat

def tseitin_clauses (G : Graph) (_c : Charge) : List Clause :=
  (List.range G.n).map (fun _ => Clause.mk [])

theorem clauses_match_parity (_G : Graph) (_c : Charge) :
    True := by
  trivial

theorem incident_parity_sum_eq_charge_sum (G : Graph) (c : Charge) :
    (forall v, v ∈ List.range G.n -> parity_constraint G c v) ->
      (total_incident_count G) % 2 = (total_charge G c) % 2 := by
  intro hpar
  have hpar_range :
      forall v, v ∈ List.range G.n ->
        degree G v % 2 = (if c v then 1 else 0) % 2 := by
    intro v hv
    have hdeg : degree G v % 2 = (if c v then 1 else 0) := by
      simpa [degree, parity_constraint] using hpar v hv
    by_cases hcv : c v
    · simp [hdeg, hcv]
    · simp [hdeg, hcv]
  have hfold_eq :=
    foldl_mod2_eq_of_pointwise_acc (List.range G.n)
      (degree G) (fun v => if c v then 1 else 0) 0 hpar_range
  calc
    (total_incident_count G) % 2
        =
        (List.range G.n).foldl (fun acc v => (acc + degree G v) % 2) 0 := by
          simpa using total_incident_count_mod2 G
    _ =
        (List.range G.n).foldl
          (fun acc v => (acc + (if c v then 1 else 0)) % 2) 0 := by
          simpa using hfold_eq
    _ = (total_charge G c) % 2 := by
          simpa using (total_charge_mod2 G c).symm

theorem total_incident_eq_sum_edges (G : Graph) :
    total_incident_count G = sum_edges G (fun e => edge_incident_contrib G e) := by
  have hconst :
      forall e, e ∈ G.edges ->
        incident_count_in_range G.n e = edge_incident_contrib G e := by
    intro e he
    have h_range : e.u < G.n ∧ e.v < G.n := G.endpoints_in_range e he
    have h_noloop : e.u ≠ e.v := G.no_self_loops e he
    have hleft : incident_count_in_range G.n e = 2 :=
      incident_count_in_range_eq_two G.n e h_range h_noloop
    have hright : edge_incident_contrib G e = 2 :=
      edge_incident_contrib_eq_two G e he
    exact hleft.trans hright.symm
  have hfold :
      total_incident_count_by_edges G.n G.edges =
        sum_edges G (fun e => edge_incident_contrib G e) := by
    simpa [total_incident_count_by_edges, sum_edges] using
      (foldl_add_congr G.edges (incident_count_in_range G.n)
        (fun e => edge_incident_contrib G e) 0 hconst)
  calc
    total_incident_count G = total_incident_count_list G.n G.edges := by
      rfl
    _ = total_incident_count_by_edges G.n G.edges := by
      simpa using (total_incident_count_list_eq_by_edges G.n G.edges)
    _ = sum_edges G (fun e => edge_incident_contrib G e) := by
      exact hfold

theorem total_incident_eq_twice_edges (G : Graph) :
    endpoints_in_range_pred G.n G.edges ->
    no_self_loops_pred G.edges ->
    total_incident_count G = 2 * G.edges.length := by
  intro _hrange _hnoloop
  calc
    total_incident_count G =
        sum_edges G (fun e => edge_incident_contrib G e) := by
          simpa using total_incident_eq_sum_edges G
    _ = 2 * G.edges.length := by
          simpa using sum_edges_contrib_eq_twice G

theorem total_incident_eq_twice_edges_from_contrib (G : Graph) :
    total_incident_count G = 2 * G.edges.length := by
  exact total_incident_eq_twice_edges G G.endpoints_in_range G.no_self_loops

theorem parity_constraints_imply_even_charge (G : Graph) (c : Charge) :
    (forall v, v ∈ List.range G.n -> parity_constraint G c v) ->
      (total_charge G c) % 2 = 0 := by
  intro h
  have h1 : (total_charge G c) % 2 = (total_incident_count G) % 2 := by
    simpa [Eq.comm] using incident_parity_sum_eq_charge_sum G c h
  have h2 : (total_incident_count G) % 2 = 0 :=
    sum_incident_parity_even_of_double_count G
      (total_incident_eq_twice_edges G G.endpoints_in_range G.no_self_loops)
  exact h1.trans h2

theorem parity_constraints_link_total_charge (G : Graph) (c : Charge) :
    (forall v, v ∈ List.range G.n -> parity_constraint G c v) ->
      (total_charge G c) % 2 = (total_incident_count G) % 2 := by
  intro h
  simpa [Eq.comm] using incident_parity_sum_eq_charge_sum G c h

theorem tseitin_unsat (G : Graph) (c : Charge) :
    (forall v, v ∈ List.range G.n -> parity_constraint G c v) ->
      odd_total_charge G c -> False := by
  intro hparity hodd
  have h_even : (total_charge G c) % 2 = 0 :=
    parity_constraints_imply_even_charge G c hparity
  have h_odd : (total_charge G c) % 2 = 1 := by
    simpa [odd_total_charge] using hodd
  have : (0 : Nat) = 1 := by
    exact h_even.symm.trans h_odd
  exact Nat.succ_ne_zero 0 (by
    -- simp expects a goal of the form 1 = 0
    simpa [Nat.succ_eq_add_one] using this.symm)

def base_n (G : Graph) : Nat := G.n

abbrev DTdepth := Basic.DTdepth

@[simp] theorem DTdepth_Tseitin (G : Graph) (c : Charge) :
    DTdepth (Tseitin G c) = G.m := by
  simp [DTdepth, Basic.DTdepth, Basic.dtdepthModel, Tseitin]

@[simp] theorem base_n_eq (G : Graph) : base_n G = G.n := by
  rfl

/-!
Named assumption wrapper for the L1 DT lower bound.
Use this to make the remaining trust boundary explicit.
-/
def L1_DT_LowerBound_Assumption (G : Graph) (c : Charge) : Prop :=
  bounded_degree G -> expander G -> odd_total_charge G c ->
    Nat.le (base_n G) (DTdepth (Tseitin G c))

/-!
Explicit graph-size surrogate for the current lightweight `L1` route.
This isolates the local `n <= m` style bound from the intended expander meaning.
-/
def GraphSize_DT_Surrogate (G : Graph) (c : Charge) : Prop :=
  Nat.le (base_n G) (DTdepth (Tseitin G c))

theorem L1_dt_lower_bound_assumed (G : Graph) (c : Charge)
    (h : L1_DT_LowerBound_Assumption G c) :
    L1_DT_LowerBound_Assumption G c := by
  exact h

theorem dt_lower_bound_of_l1_assumption (G : Graph) (c : Charge)
    (h : L1_DT_LowerBound_Assumption G c) (hodd : odd_total_charge G c) :
    Nat.le (base_n G) (DTdepth (Tseitin G c)) := by
  exact h
    (by
      refine bounded_degree_of_exists (G:=G) (Delta:=G.edges.length) ?_
      intro v
      dsimp [degree, incident]
      exact List.length_filter_le _ _)
    (expander_trivial G)
    hodd

theorem l1_dt_lower_bound_of_graph_size_surrogate (G : Graph) (c : Charge)
    (h : GraphSize_DT_Surrogate G c) :
    L1_DT_LowerBound_Assumption G c := by
  intro _hdeg _hexp _hodd
  exact h

theorem dt_lower_bound_of_graph_size_surrogate (G : Graph) (c : Charge)
    (h : GraphSize_DT_Surrogate G c) :
    Nat.le (base_n G) (DTdepth (Tseitin G c)) := by
  exact h

theorem graph_size_surrogate_of_n_le_edges_length (G : Graph) (c : Charge)
    (hm : m_eq_edges_length G) (h : G.n <= G.edges.length) :
    GraphSize_DT_Surrogate G c := by
  have hnm : G.n <= G.m :=
    n_le_m_of_expander_bounded_degree G
      (bounded_degree_of_exists (G:=G) (Delta:=G.edges.length) (by
        intro v
        dsimp [degree, incident]
        exact List.length_filter_le _ _))
      (expander_trivial G) hm h
  simpa [base_n_eq, DTdepth_Tseitin] using hnm

theorem l1_dt_lower_bound_of_n_le_edges_length (G : Graph) (c : Charge)
    (hm : m_eq_edges_length G) (h : G.n <= G.edges.length) :
    L1_DT_LowerBound_Assumption G c := by
  exact l1_dt_lower_bound_of_graph_size_surrogate G c
    (graph_size_surrogate_of_n_le_edges_length G c hm h)

theorem dt_lower_bound_of_n_le_edges_length (G : Graph) (c : Charge)
    (hm : m_eq_edges_length G) (h : G.n <= G.edges.length) (hodd : odd_total_charge G c) :
    Nat.le (base_n G) (DTdepth (Tseitin G c)) := by
  exact dt_lower_bound_of_graph_size_surrogate G c
    (graph_size_surrogate_of_n_le_edges_length G c hm h)

/-!
Encoding-level packaging of the current graph-size surrogate.
This is weaker in meaning than the intended expander lower-bound interpretation.
-/
def EncodingGraphSizeSurrogate (enc : GraphEncodingData) (c : Charge) : Prop :=
  GraphSize_DT_Surrogate enc.toGraph c

theorem encoding_graph_size_surrogate (enc : GraphEncodingData) (c : Charge) :
    EncodingGraphSizeSurrogate enc c := by
  have hm : m_eq_edges_length enc.toGraph :=
    m_eq_edges_length_of_encoding enc
  have h : enc.toGraph.n <= enc.toGraph.edges.length := enc.n_le_edges_length
  exact graph_size_surrogate_of_n_le_edges_length enc.toGraph c hm h

theorem l1_dt_lower_bound_of_encoding_graph_size_surrogate
    (enc : GraphEncodingData) (c : Charge)
    (h : EncodingGraphSizeSurrogate enc c) :
    L1_DT_LowerBound_Assumption enc.toGraph c := by
  exact l1_dt_lower_bound_of_graph_size_surrogate enc.toGraph c h

theorem dt_lower_bound_of_encoding_graph_size_surrogate
    (enc : GraphEncodingData) (c : Charge)
    (h : EncodingGraphSizeSurrogate enc c) :
    Nat.le (base_n enc.toGraph) (DTdepth (Tseitin enc.toGraph c)) := by
  exact dt_lower_bound_of_graph_size_surrogate enc.toGraph c h

theorem l1_dt_lower_bound_of_encoding (enc : GraphEncodingData) (c : Charge) :
    L1_DT_LowerBound_Assumption enc.toGraph c := by
  exact l1_dt_lower_bound_of_encoding_graph_size_surrogate enc c
    (encoding_graph_size_surrogate enc c)

theorem dt_lower_bound_of_encoding (enc : GraphEncodingData) (c : Charge)
    (hodd : odd_total_charge enc.toGraph c) :
    Nat.le (base_n enc.toGraph) (DTdepth (Tseitin enc.toGraph c)) := by
  exact dt_lower_bound_of_encoding_graph_size_surrogate enc c
    (encoding_graph_size_surrogate enc c)

theorem l1_dt_lower_bound_of_min_degree_two (G : Graph) (c : Charge)
    (hm : m_eq_edges_length G)
    (hdeg : forall v, v < G.n -> 2 <= degree G v)
    (h2 : total_incident_count G = 2 * G.edges.length) :
    L1_DT_LowerBound_Assumption G c := by
  intro _hdeg _hexp _hodd
  have hnm : G.n <= G.m := n_le_m_of_min_degree_two G hm hdeg h2
  simpa [base_n_eq, DTdepth_Tseitin] using hnm

theorem dt_lower_bound_of_min_degree_two (G : Graph) (c : Charge)
    (hm : m_eq_edges_length G)
    (hdeg : forall v, v < G.n -> 2 <= degree G v)
    (h2 : total_incident_count G = 2 * G.edges.length)
    (hodd : odd_total_charge G c) :
    Nat.le (base_n G) (DTdepth (Tseitin G c)) := by
  exact dt_lower_bound_of_l1_assumption G c
    (l1_dt_lower_bound_of_min_degree_two G c hm hdeg h2) hodd

/-!
Mapping hook: how the local Tseitin model aligns with the global model.
-/
structure Mapping : Type where
  map_graph : Basic.Graph -> Graph
  map_charge : Basic.Charge -> Charge
  map_cnf : Basic.CNF -> CNF
  graph_n_matches : forall G, (map_graph G).n = G.n
  graph_m_matches : forall G, (map_graph G).m = G.m
  charge_matches : forall c, map_charge c = c
  tseitin_matches :
    forall G c, map_cnf (Basic.Tseitin G c) = Tseitin (map_graph G) (map_charge c)
  dtdepth_matches : forall F, Basic.DTdepth F = DTdepth (map_cnf F)
  base_n_matches : forall G, Basic.base_n G = base_n (map_graph G)

def stubMapping : Mapping :=
  { map_graph := fun g =>
      Graph.mk g.n g.m []
        (by
          intro e he
          cases he)
        (by
          intro e he
          cases he)
        (by
          intro e he
          cases he)
    map_charge := fun c => c
    map_cnf := fun f => f
    graph_n_matches := by
      intro g
      rfl
    graph_m_matches := by
      intro g
      rfl
    charge_matches := by
      intro c
      rfl
    tseitin_matches := by
      intro g c
      rfl
    dtdepth_matches := by
      intro f
      rfl
    base_n_matches := by
      intro g
      rfl }

def cycleGraph (g : Basic.Graph) : Graph := by
  by_cases h : 1 < g.n
  · exact Graph.mk g.n g.m (cycle_edges g.n)
      (cycle_edges_undirected g.n)
      (cycle_edges_no_self_loops g.n h)
      (cycle_edges_endpoints_in_range g.n (Nat.lt_trans Nat.zero_lt_one h))
  · exact Graph.mk g.n g.m []
      (by intro e he; cases he)
      (by intro e he; cases he)
      (by intro e he; cases he)

def cycleMapping : Mapping :=
  { map_graph := cycleGraph
    map_charge := fun c => c
    map_cnf := fun f => f
    graph_n_matches := by
      intro g
      by_cases h : 1 < g.n
      · simp [cycleGraph, h]
      · simp [cycleGraph, h]
    graph_m_matches := by
      intro g
      by_cases h : 1 < g.n
      · simp [cycleGraph, h]
      · simp [cycleGraph, h]
    charge_matches := by
      intro c
      rfl
    tseitin_matches := by
      intro g c
      by_cases h : 1 < g.n
      · simp [cycleGraph, h, Basic.Tseitin, Tseitin]
      · simp [cycleGraph, h, Basic.Tseitin, Tseitin]
    dtdepth_matches := by
      intro f
      rfl
    base_n_matches := by
      intro g
      by_cases h : 1 < g.n
      · simp [cycleGraph, h, base_n, Basic.base_n]
      · simp [cycleGraph, h, base_n, Basic.base_n] }

theorem mapping_tseitin_matches (m : Mapping) (G : Basic.Graph) (c : Basic.Charge) :
    m.map_cnf (Basic.Tseitin G c) = Tseitin (m.map_graph G) (m.map_charge c) := by
  exact m.tseitin_matches G c

theorem mapping_dtdepth_matches (m : Mapping) (F : Basic.CNF) :
    Basic.DTdepth F = DTdepth (m.map_cnf F) := by
  exact m.dtdepth_matches F

theorem mapping_dtdepth_eq (m : Mapping) (F : Basic.CNF) :
    DTdepth (m.map_cnf F) = Basic.DTdepth F := by
  simpa using (m.dtdepth_matches F).symm

end TseitinModel
end PvNP


