import PEqualNP.Defs

-- The graph is the parent's 21-edge list. A first gate is specified by its
-- operation (false for AND, true for OR) and its two vertex indices. The
-- suffix consists of finite instructions. Finite wire indices also select
-- the output. Missing and forward wires have the root circuit's false default.
-- The test rows are exactly the 21 two-vertex edges and the 37 maximal
-- independent sets. At a positive boundary row, switching off any true bit
-- destroys the edge. At a negative boundary row, switching on any false bit
-- creates an edge. The output must match the graph on these 58 rows.
theorem PEqualNP.Outside.R_meta_971_58
    (normalize :
      let target := (fun x : Fin 14 → Bool => ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ s : ℕ, C.size ≤ s →
      (∀ x, C.eval (List.ofFn x) = true ↔ target x) →
      ∃ first ∈ ([(false, 0, 7), (true, 0, 1), (true, 0, 7), (true, 0, 9)] : List (Bool × ℕ × ℕ)),
        ∃ p : Fin (s - 1) → Bool × Fin (13 + s) × Fin (13 + s), ∃ o : Fin (14 + s),
          let gate := fun (g : Bool × ℕ × ℕ) =>
              PEqualNP.CircuitLowerBounds.Gate.mk
                (cond g.1 PEqualNP.CircuitLowerBounds.GateOp.or PEqualNP.CircuitLowerBounds.GateOp.and)
                [g.2.1, g.2.2]
          let gs := (List.ofFn p).map fun g => gate (g.1, g.2.1.val, g.2.2.val)
          let D := PEqualNP.CircuitLowerBounds.Circuit.mk (gate first :: gs) o.val
          ∀ x, (∀ i, (x i = true ↔ target x) →
            (target (Function.update x i (!(x i))) ↔ ¬ target x)) →
            (D.eval (List.ofFn x) = true ↔ target x))
    (edgeAnd :
      let target := (fun x : Fin 14 → Bool => ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)
      ¬ (∃ p : Fin 25 → Bool × Fin 39 × Fin 39, ∃ o : Fin 40,
          let gate := fun (g : Bool × ℕ × ℕ) =>
              PEqualNP.CircuitLowerBounds.Gate.mk
                (cond g.1 PEqualNP.CircuitLowerBounds.GateOp.or PEqualNP.CircuitLowerBounds.GateOp.and)
                [g.2.1, g.2.2]
          let gs := (List.ofFn p).map fun g => gate (g.1, g.2.1.val, g.2.2.val)
          let D := PEqualNP.CircuitLowerBounds.Circuit.mk (gate (false, 0, 7) :: gs) o.val
          ∀ x, (∀ i, (x i = true ↔ target x) →
            (target (Function.update x i (!(x i))) ↔ ¬ target x)) →
            (D.eval (List.ofFn x) = true ↔ target x)))
    (firstOr :
      let target := (fun x : Fin 14 → Bool => ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)
      ∀ first ∈ ([(true, 0, 1), (true, 0, 7), (true, 0, 9)] : List (Bool × ℕ × ℕ)),
      ¬ (∃ p : Fin 25 → Bool × Fin 39 × Fin 39, ∃ o : Fin 40,
          let gate := fun (g : Bool × ℕ × ℕ) =>
              PEqualNP.CircuitLowerBounds.Gate.mk
                (cond g.1 PEqualNP.CircuitLowerBounds.GateOp.or PEqualNP.CircuitLowerBounds.GateOp.and)
                [g.2.1, g.2.2]
          let gs := (List.ofFn p).map fun g => gate (g.1, g.2.1.val, g.2.2.val)
          let D := PEqualNP.CircuitLowerBounds.Circuit.mk (gate first :: gs) o.val
          ∀ x, (∀ i, (x i = true ↔ target x) →
            (target (Function.update x i (!(x i))) ↔ ¬ target x)) →
            (D.eval (List.ofFn x) = true ↔ target x))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  intro C hm hf
  apply Nat.le_of_not_lt
  intro hs
  obtain ⟨first, hfirst, hprog⟩ := normalize C hm 26 (by omega) hf
  rcases List.mem_cons.mp hfirst with h | h
  · subst first
    exact edgeAnd hprog
  · exact firstOr first h hprog
