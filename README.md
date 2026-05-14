# The Gentzen-Lean Style in Mathematical Logic

This repository contains formal proofs in Lean 4, designed to maintain a (nearly) 1:1 correspondence with Gentzen-like natural deduction derivations.

## 📖 Abstract
**Introduction:** The objective of this work is to bridge the gap between traditional Gentzen-style logical derivations and interactive theorem proving in Lean 4 tactic mode by exploring the possibility of a strict 1:1 mapping of the two formalisms.

**Success of Local Rules:** Standard linear inference rules—such as Modus Ponens (MP), Modus Tollens (MT), Disjunctive Syllogisms (DS1/DS2), and Conjunction rules (∧E/∧I) — map perfectly onto explicit Lean expressions. Using `have` structures for intermediate steps preserves exact granularity. Our analysis is restricted to derivations containing at most a single application of any meta-rule (IP, CP, or PEC). Even within this scope, a notable exception is the disjunction rule ((PC): A ∨ B, A → C, B → C ⊢ C), for which we provide a counterexample that cannot be represented in a 1:1 fashion. Consequently, both this limitation and the challenges of nested meta-rules lead us directly to the problem of *Implicit Structural Closure*.

**The Limit of Implicit Structural Closure:** Lean’s proof engine operates on a goal-driven mechanism. When a final target type is synthesized, closing commands like `exact` or `contradiction` immediately terminate subgoals internally. This automation introduces a structural boundary: Lean obscures the distinction between constructing the final proposition and discharging the surrounding meta-rule context (e.g., CP or IP).

**Branching and Asymmetry Boundaries:** The absolute 1:1 mapping encounters a conceptual bottleneck in rules that trigger structural splits (such as Disjunction Elimination via `rcases` or `by_cases`). Forcing a strict line-by-line derivation creates a structural asymmetry, wherein the tactic command must simultaneously serve as both the structural announcement and the implicit, immediate assumption of the first branch.

**The Hybrid Derivation Paradigm:** To escape artificial proof constructs while maintaining absolute explicitness, we propose a *Hybrid Gentzen-Lean Style*. By embedding unnumbered, metadata-rich Lean comments alongside the strictly numbered Gentzen sequence, the proof architecture remains readable for human logicians and transparent for machine analysis. This coexistence preserves the deductive linearity of natural deduction without hiding Lean’s internal goal transformations.

## 📝 Example: Hybrid Gentzen-Lean Style
Here is a preview of how the hybrid sequence integrates Lean tactics with numbered Gentzen steps:

```lean
example {P Q R : Prop} : ((P ∧ R) ∨ (Q ∧ R)) → R := by {
  intro h_disj                           -- 1 [(P∧R)∨(Q∧R)]CP
  rcases h_disj with hPR | hQR           -- Lean: PC with [P∧R]PC1 and [Q∧R]PC2
  have hPR : P∧R := hPR                  -- 2 [P∧R]PC1
  exact hPR.right                        -- 3 R by ∧-Elimination2 from 2
  have hQR : Q∧R := hQR                  -- 4 [Q∧R]PC2    
  exact hQR.right                        -- 5 R by ∧-Elimination2 from 4
                                         -- Lean: pending goal(s) silently closed
------------------------------------------------------------------------------------
                                         -- 6 R by PC from 2-5
                                         -- 7 ((P ∧ R) ∨ (Q ∧ R)) → R by CP from 1-6
}
```

## 🚀 Try it Online
Since this project is optimized for the web-based version of Lean 4, you don't need to install anything locally.

1. Open the [Lean 4 Web Editor](https://lean-lang.org).
2. Copy the code from any `.lean` file in this repository.
3. Paste it into the web editor to see the interactive proof state!

## 📈 Progress
- [x] **Propositional Logic**: Basic Rules     ([The Gentzen-Lean Style in Mathematical Logic 1](https://github.com/o-netzer/LeanProving/blob/main/THE%20GENTZEN%E2%80%93LEAN%20PROVING%20STYLE%20IN%20MATHEMATICAL%20LOGIC%201.lean))

- [x] **Propositional Logic**: Meta-rules      ([The Gentzen-Lean Style in Mathematical Logic 1](https://github.com/o-netzer/LeanProving/blob/main/THE%20GENTZEN%E2%80%93LEAN%20PROVING%20STYLE%20IN%20MATHEMATICAL%20LOGIC%201.lean))

- [ ] **Propositional Logic**: Derived Rules
- [ ] **First Order Logic** with Identity
