# The Gentzen-Lean Styles in Mathematical Logic

This repository contains formal proofs in Lean 4, designed to maintain a (nearly) 1:1 correspondence with Gentzen-like natural deduction derivations.

## 1  Propositional Logic

## [Part 1](https://github.com/o-netzer/LeanProving/blob/main/THE%20GENTZEN%E2%80%93LEAN%20PROVING%20STYLE%20IN%20MATHEMATICAL%20LOGIC%201.lean)

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

## [Part 2](https://github.com/o-netzer/LeanProving/blob/main/THE%20GENTZEN%E2%80%93LEAN%20PROVING%20STYLE%20IN%20MATHEMATICAL%20LOGIC%202.lean)


## 📖 Abstract
## Abstract 
**Introduction** In the second part of this paper on Gentzen-Lean proof styles, we continue
 to formalize further rules of our propositional natural deduction system within Lean 4,
 presenting their applications in the hybrid Gentzen-Lean style. Concurrently, we introduce a
 novel, non-hybrid approach right from the outset: Gentzen-Lean Subproofing. This method
 systematically resolves the issue of Lean's "silent closing of pending goals" (the invisibility
 of discharging assumptions), establishing—with only minor structural overhead—a precise 1:1 
 correspondence between Lean code and traditional Gentzen-style derivations. Consequently,
 all subsequent proofs in this paper, which primarily center around equivalence theorems,
 are performed and contrasted in both styles.
 
 **Structured Lean Tactic Proofs with Named Subproofs ("Subproofing")**
 While highly elegant, the subproofing methodology initially encounters several structural
 challenges that seemingly conflict with the 1:1 desideratum. This paper identifies these
 obstacles and provides explicit architectural solutions:
 
 1) The Absence of Explicit Top-Level Discharges:
 For standard constructive proofs, Lean often terminates the  environment immediately after
 the last inner tactic, leaving no syntactic room for a final closure. We show  that explicitly
 repeating the target theorem statement as a subproof skeleton layer (have tbp1) at the very
 beginning provides the necessary scope to make the ultimate discharge visible.
 2) The Redundancy and Doubling of Closures:
 In deep multi-branch derivations (such as equivalence introductions), active closing statements
 can prematurely break the proof scope. To overcome this, we introduce the technique of
 "Discharge on Hold" (Passive Discharge). This mechanism allows the logician to explicitly
 document a discharge via a have statement, which Lean successfully registers in the local
 context while postponing the active execution to a later merging step.
 3) Granularity and Structural Complexity:
 To assist the reader in navigating complex nested proofs, we outline a methodical Top-Down
 Structural Refinement procedure. By utilizing Lean’s 'sorry' keyword, writers
 can incrementally construct and verify the multi-layered subproof skeleton before filling
 the atomic gaps with logical deductions.
 4) The Collapse of Global Goal Repetition:
 We reveal a fundamental structural law of the subproofing skin: whenever a derivation features
 a classical or multi-branch rule (such as Proof by Cases or Indirect Proof) at its very root
 rather than a constructive introduction, the enclosing global goal repetition naturally
 collapses. The proof starts directly with the respective by_cases/by_contra skeletons, proving
 that the style organically adapts to the top-level topology of the Gentzen tree.
 5) Explicit Encapsulation of Indirect Proofs: We introduce a custom helper rule (ip_rule) that
 encapsulates Lean's inline by_contra mechanism. This rule enables the reader to visually
 anchor a classical Reductio ad absurdum to an explicit contradiction formula (A ∧ ¬A) and its
 corresponding edge in the subproof skeleton.
 
 Ultimately, Part 2 demonstrates that Lean 4 is not only a tool for formal verification but can
 be strictly disciplined to mirror the visual, step-by-step beauty of human-readable textbook
 logic. Clarity and explicitness serve as the guiding principles for the Gentzen-Lean styles.
 Crucially, this step-by-step rigor does not equate to slow, granular progression; by leveraging
 powerful high-level theorems and lemmas, both Gentzen-Lean styles allows for massive logical
 leaps, proving that pedantic precision can seamlessly coexist with elegant and rapid derivation.
 
## 📝 Example: Hybrid Gentzen-Lean Style VS Gentzen Lean Subproofing Style
As expected, in our hybrid Gentzen-Lean style, a simple chain of two implications results
in Lean "swallowing" the final discharge (CP1): 
```lean
--formula
example (P Q : Prop) : (P → (Q → P)) := by {
  intro hP                        -- 1 [P]CP1
  intro hQ                        -- 2 [Q]CP2
  have hP : P := trivial_arg hP   -- 3 P by TA from 1
  exact hP                        -- 4 Q→P by CP2 from 2-3
                                  -- Lean: pending goal(s) closed
  -----------------------------------------------------------------
                                  -- 5 P → (Q → P) by CP1 from 1-4
}
/-
In contrast, the subproofing approach results in an explicit closure of each
individual goal:
-/

-- Complete discharge
example (P Q : Prop) : (P → (Q → P)) := by {
  have tbp1 : (P → (Q → P)) := by {  
    intro hP                          -- 1 [P]CP1
    have tbp2 : (Q → P) := by {
      intro hQ                        -- 2 [Q]CP2
      exact trivial_arg hP            -- 3 P by TA from 1
    }
    exact tbp2                        -- 4 Q → P by CP2 from 2-3
  }
  exact tbp1                          -- 5 P → (Q → P) by CP1 from 1-4
}
/-

Note that both derivations (numbered lines) are identical. Most important of all:


--------------------------------------------------------------------------------
If we disregard the structural overhead of the subproof declarations — namely 
the 'have tbpn' keywords and the repetition of the formulas — the remaining lines, 
including the validating 'exact' statements, maintain a precise 1:1 correspondence 
with the steps and discharges of a traditional natural deduction derivation!
-------------------------------------------------------------------------------- 
```

## 🚀 Try it Online
Since this project is optimized for the web-based version of Lean 4, you don't need to install anything locally.

1. Open the [Lean 4 Web Editor](https://live.lean-lang.org/).
2. Copy the code from any `.lean` file in this repository.
3. Paste it into the web editor to see the interactive proof state!

## 📈 Progress
- [x] **Propositional Logic**: Basic Rules     ([The Gentzen-Lean Style in Mathematical Logic 1](https://github.com/o-netzer/LeanProving/blob/main/THE%20GENTZEN%E2%80%93LEAN%20PROVING%20STYLE%20IN%20MATHEMATICAL%20LOGIC%201.lean))

- [x] **Propositional Logic**: Meta-rules      ([The Gentzen-Lean Style in Mathematical Logic 1](https://github.com/o-netzer/LeanProving/blob/main/THE%20GENTZEN%E2%80%93LEAN%20PROVING%20STYLE%20IN%20MATHEMATICAL%20LOGIC%201.lean))

- [ ] **Propositional Logic**: Derived Rules
- [ ] **First Order Logic** with Identity
