import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- On the input supported by the two endpoints, assign them cost one.
-- An unavailable input or wire costs three. An AND adds its costs, an OR takes
-- the minimum, and all costs are capped at three. Empty AND has cost zero.
-- For a circuit computing the edge function, cost two witnesses a parse tree
-- using each endpoint once. A single repeated endpoint would accept a singleton.
-- The normalization child may change the circuit and retain a constant fraction
-- of the edges. This permits useful changes to shared subcircuits: duplicating
-- the output at one final AND can otherwise destroy every cost-two witness.

-- To count the witnessed edges, keep at each wire the set of variables with a
-- one-leaf parse and whether the wire has a zero-leaf parse. An OR takes the
-- union of its input sets. An AND inherits a set when the opposite operand
-- has a zero-leaf parse. Thus each gate needs at most one binary union.
-- The lowest common ancestor of the two leaves is an AND. On its path to the
-- output every AND sibling admits a zero-leaf parse. The two one-leaf sets
-- at this gate therefore form a complete bipartite subgraph. They are
-- disjoint because a shared vertex would make the output true on a singleton.
-- With no four-cycle, this product is a star. Neither operand admits a
-- zero-leaf parse, so the product gate costs no union in the one-leaf sets.
-- For a center with t products covering d distinct leaves, tracing their t
-- leaf sets back to inputs needs at least d minus t nontrivial union gates.
-- Unions of size at least two cannot serve distinct centers, since two
-- common neighbors would form a four-cycle. Summing charges each witnessed
-- edge to either a product or a union, at a total cost at most D.size.

theorem PEqualNP.Outside.R_meta_1710_27
    (normalize : ∃ a : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧
        D.size ≤ a * (C.size + 1) ∧ G.edgeFinset.card ≤ a *
        (G.edgeFinset.filter fun e => ∃ u v : Fin n, e = s(u,v) ∧
          ((D.gates.foldl (fun (w : List Nat) g =>
            let xs := g.inputs.map (fun i => w.getD i 3)
            w ++ [cond (g.op.eval []) (min 3 xs.sum) (xs.foldr min 3)])
            (List.ofFn (fun i : Fin n => cond (decide (i = u ∨ i = v)) 1 3))).getD D.output 3 = 2)).card)
    (countTwo : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
        (G.edgeFinset.filter fun e => ∃ u v : Fin n, e = s(u,v) ∧
          ((D.gates.foldl (fun (w : List Nat) g =>
            let xs := g.inputs.map (fun i => w.getD i 3)
            w ++ [cond (g.op.eval []) (min 3 xs.sum) (xs.foldr min 3)])
            (List.ofFn (fun i : Fin n => cond (decide (i = u ∨ i = v)) 1 3))).getD D.output 3 = 2)).card ≤ D.size) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨a, ha⟩ := normalize
  refine ⟨a * a, ?_⟩
  intro n G inst hd hg C hm hf
  have hfun : circuitFun n C = graphFun G ∅ := by
    funext x
    change circuitFun n C x =
      (decide (∃ v ∈ (∅ : Finset (Fin n)), x v = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    exact congrFun hf x
  obtain ⟨D, hD, hDC, hs, he⟩ := ha n G hd hg C hm hfun
  have hcount := countTwo n G hg D hD (hDC.trans hfun)
  calc
    _ ≤ _ := he
    _ ≤ a * D.size := Nat.mul_le_mul_left _ hcount
    _ ≤ a * (a * (C.size + 1)) := Nat.mul_le_mul_left _ hs
    _ = _ := (Nat.mul_assoc _ _ _).symm
