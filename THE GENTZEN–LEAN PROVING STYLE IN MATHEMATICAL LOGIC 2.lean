-- Tested on live.lean-lang.org
-- Author: Oliver Netzer, http://www.linkedin.com/in/onet2015, https://github.com/o-netzer/LeanProving
import Mathlib.Tactic
import Mathlib.Logic.Basic
open Classical


/-!
# THE GENTZEN–LEAN PROVING STYLES IN MATHEMATICAL LOGIC

					            Part 2


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



-------------------------------
C O N T E N T S
-------------------------------


1.6       More Derived Rules
1.6.1     Structured Lean Tactic Proofs with Named Subproofs ("Subproofing")
1.6.2     (EQUI)  A → B, B → A ⊢ A ↔ B            (Equivalence Intro)
1.6.3     (EQUI∧) (A → B) ∧ (B → A) ⊢ A ↔ B       (EquivalenceIntro∧)
1.6.4     (EQUE1) A ↔ B ⊢ A → B                   (Equivalence Elimination 1)
1.6.5     (EQUE2) A ↔ B ⊢ B → A                   (Equivalence Elimination 2)
1.6.5.1   Top-Down Structural Refinement: Developing Complex Subproofs Inkrementally
1.6.6     (SUBST) Meta-Rules Addendum: The Substitution Rule (Substitution of Equivalents)
1.6.7     (EQUS)  (A ↔ B) ⊢ (B ↔ A)               (Symmetry of Equivalence)
1.6.8     Proofs by Equivalence Transformations



-- 1.6   More Derived Rules

Some rules within our system of propositional logic can be derived from others;
these are the logically redundant rules: (TA), (PC), and (MT). In this section, 
we will examine several additional useful rules and analyze their derivations 
using our hybrid Gentzen-Lean style. Furthermore, we will introduce an alternative, 
non-hybrid style of Lean proving that centers around subproof-oriented natural deduction.





1.6.1 Structured Lean Tactic Proofs with Named Subproofs ("Subproofing")

There is a systematic way to address Lean's tendency to silently close pending
goals (the "invisibility of discharging assumptions"). The core idea is to employ
named subproofs whenever an assumption is introduced, ensuring an explicit discharge 
at the end of the block. 

As observed in Section 1.4.2, nested conditional proofs are excellent examples for
illustrating how Lean silently (and sometimes massively) closes pending goals.

To ensure previous results remain accessible for reuse, we open a namespace 
(which terminates with the 'end' keyword at the bottom of this file).

-/
--------------------------------------------------------------------------------
namespace propositional_logic

--from Section 1.3.14
def dis_prem {A B C : Prop} (hAB : A ∨ B) (hAC : A → C) (hBC : B → C) : C :=
  Or.elim hAB hAC hBC


-- short tactic notation for the Trivial Argument (TA)
theorem trivial_arg  {A : Prop} (h : A) : A := by {
  exact h
}
--------------------------------------------------------------------------------

/-
As expected, in our hybrid Gentzen-Lean style, a simple chain of two implications results
in Lean "swallowing" the final discharge (CP1): 
-/

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

In this setup, we observe two subproofs, each ending with a closing curly bracket 
followed by an 'exact' statement:

  have tbp1 : (P → (Q → P)) := by {...

    have tbp2 : (Q → P) := by {...

    }
    exact tbp2
  }
  exact tbp1

We refer to this structural pattern as the "subproof skeleton." Based on this example, 
we can outline several core characteristics of the subproofing method:

1) Visual Alignment and Scope
Every subproof is initiated by the keyword 'have', followed by an identifier 'tbpn' 
(where n ∈ {1, 2, 3, ...} and 'tbp' stands for "to be proved"). The corresponding 
closing curly bracket is vertically aligned with the start of its block and is 
immediately followed by its validating 'exact' statement. 

2) Root-Dependent Goal Repetition (CP-Skeletons)
For theorems whose Gentzen derivation tree features a Conditional Proof (CP) at its root, 
the subproofing style opens with an explicit repetition of the target goal (e.g., 'have tbp1...'). 
This repetition creates the necessary structural scope to guarantee that the final 
top-level discharge can be stated explicitly via an 'exact' command. Without this initial 
skeleton line, there is no syntactic room left to explicitly close the ultimate goal, 
as Lean terminates the proof environment immediately after the last inner block is resolved.

If we look at the conditional example without this initial repetition of the goal, 
the absence of an explicit final closure becomes instantly apparent in the code:
-/

-- No complete discharge displayed (the top-level formula is not wrapped in a subproof)
example (P Q : Prop) : (P → (Q → P)) := by {
  intro hP
  have tbp2 : Q → P := by {
    intro hQ
    exact trivial_arg hP
  }
  exact tbp2 -- Q → P
}
-- No space left for closing the last goal: exact tbp1 -- 5 P → (Q → P) by CP1 from 1-4

/-
Note that while this repetition is a defining characteristic for top-level CP derivations, 
we will later encounter vital exceptions (such as top-level IP and PC derivations) 
where a global goal repetition is structurally impossible.
-/

/-
3) Lean's Implicit Goal Management
Lean accepts the completeness of the proof even without an explicit top-level discharging 
statement. This behavior is due to Lean’s block-scoping mechanism and implicit goal tracking.

When a subproof is enclosed in curly brackets '{ ... }', Lean isolates that specific 
sub-goal. Once the tactics inside that block successfully close it, Lean returns to the 
outer scope and updates the local context with the newly proven proposition. Therefore, 
the explicit 'exact' statements in our skeleton primarily serve as a visual anchor to 
make this structural closing of goals transparent and human-readable.

4) Nesting Capabilities
The number of nested CP-subproofs (as well as other nested subproofs) does not affect 
the structural integrity of the method or the ability to close each goal:
-/

--Complete discharge with three consecutive implications
example (P Q : Prop) : (P → (P → (Q → P))) := by {
  have tbp1 : (P → (P → (Q → P))) := by {
    intro h1P
    have tbp2 : P → (Q → P) := by {
      intro h2P
      have tbp3 : (Q → P) := by {
        intro hQ
        exact trivial_arg h1P 
      }
      exact tbp3 --Q → P
    }
    exact tbp2   -- P → (Q → P)
  }
  exact tbp1     -- P → (P → (Q → P))
}
/-

5) Structural Inflation and Over-Subproofing
Not every subproof construction is useful; over-subproofing can compromise the 
clarity of the proof skeleton. To demonstrate this phenomenon, we will analyze a proof 
involving two nested conditionals and one indirect proof (which is, of course, a more 
complex way to prove this theorem than necessary).
-/
 

--formula, nested CPs and IP in Gentzen-Lean hybrid style
example {P Q : Prop} : (P ∨ Q) → (¬P → Q) := by {
  intro h1                                -- 1 [P∨Q]CP1
  intro h2                                -- 2 [¬P]CP2
  by_contra hnQ                           -- 3 [¬Q]IP
  have h3 : P := Or.resolve_right h1 hnQ  -- 4 P by DS2 from 1,3
  have cont : P ∧ ¬P := And.intro h3 h2   -- 5 P∧¬P by ∧-Intro from 2,4
  contradiction                           -- 6 Q by IP from 3-5
  ----------------------------------------------------------------------
                                          --   Lean: pending goal(s) silently closed
                                          -- 7 ¬P → Q by CP2 from 2-6                           
                                          -- 8 (P ∨ Q) → (¬P → Q) by CP1 from 1-7
}

-- Subproofing taken to an extreme (questionable duplication in line 7)
example {P Q : Prop} : (P ∨ Q) → (¬P → Q) := by {
  have tbp1 : (P ∨ Q) → (¬P → Q) := by {
    intro h1                                    -- 1 [P∨Q]CP1
    have tbp2 : ¬P → Q := by {
      intro h2                                  -- 2 [¬P]CP2
      have tbp3 : Q := by {
        by_contra hnQ                           -- 3 [¬Q]IP
        have h3 : P := Or.resolve_right h1 hnQ  -- 4 P by DS2 from 1,3
        have cont : P ∧ ¬P := And.intro h3 h2   -- 5 P∧¬P by ∧-Intro from 2,4
        contradiction                           -- 6 Q by IP from 3-5 
        }                                
      exact tbp3                                -- 7 Q by ???
    }
    exact tbp2                                  -- 8 ¬P→Q by CP2 from 2-6/7 ???
  }
  exact tbp1                                    -- 9 (P ∨ Q) → (¬P → Q) by CP1 from 1-7/8 ???
}

/-
Note that tbp3 initiates a subproof without introducing a new variable via an 'intro' 
statement, even though it contains a 'by_contra' assumption. However, this assumption is 
already discharged at the end of the subproof block (via 'contradiction'), and the 
subsequent 'exact tbp3' attempts to close the exact same goal (Q) once more. 

In this case, the principle of "more is better" is counterintuitive; there is no logical 
operation in natural deduction that could justify step 7 of this derivation. If we want 
to remain within standard inline tactics, the cleaner solution is to renounce an extra 
subproof for Q and let the indirect proof handle the discharge inline:
-/

-- complete discharge (Inline IP handling)
example {P Q : Prop} : (P ∨ Q) → (¬P → Q) := by {
  have tbp1 : (P ∨ Q) → (¬P → Q) := by {
    intro h1                                  -- 1 [P∨Q]CP1
    have tbp2 : ¬P → Q := by {
      intro h2                                -- 2 [¬P]CP2
      by_contra hnQ                           -- 3 [¬Q]IP
      have h3 : P := Or.resolve_right h1 hnQ  -- 4 P by DS2 from 1,3
      have cont : P ∧ ¬P := And.intro h3 h2   -- 5 P∧¬P by ∧-Intro from 2,4
      contradiction                           -- 6 Q by IP from 3-5 
    }
    exact tbp2                                -- 7 ¬P→Q by CP2 from 2-6
  }
  exact tbp1                                  -- 8 (P ∨ Q) → (¬P → Q) by CP1 from 1-7
}
/-
As we will see in the upcoming sections, if a strict 1:1 correspondence for such 
indirect steps is explicitly desired without causing structural inflation, we can 
employ a dedicated helper rule ('ip_rule') to eleganty bind the IP-discharge to 
its own subproof skeleton.
-/

/-
6) Argument Forms and Disjunction Elimination (Proof by Cases)

Thus far, we have only considered pure formulas in our subproofing style. We now turn 
to argument forms, which require us to introduce the premises at the very beginning of 
the derivation. Additionally, we will demonstrate how to structurally integrate proofs 
by cases (PCs) into the subproofing framework.
-/

-- argument form in the hybrid Gentzen-Lean style
example  (P Q : Prop) (h1 : P → Q) : (¬P ∨ Q) := by {
  have h1 : P → Q := h1             -- 1 [P→Q]Pr
  by_cases hP : P                   -- 2 [P]PEC1
  have hQ : Q := h1 hP              -- 3 Q by Modus Ponens from 1,2
  exact Or.inr hQ                   -- 4 ¬P ∨ Q by ∨-Intro2 from 3
  have hnP : ¬P := hP               -- 5 [¬P]PEC2
  have goal2 : ¬P ∨ Q := Or.inl hP  -- 6 ¬P ∨ Q by ∨-Intro1 from 5
  exact goal2                       -- 7 ¬P ∨ Q by PEC from 2-6
}

/-
When migrating to subproofing, we first place the premises as 'have' statements. 
However, applying the standard inline 'by_cases' tactic inside a subproof skeleton 
reveals a structural problem:
-/

--argument form with subproofing (problematic)
example  (P Q : Prop) (h1 : P → Q) : (¬P ∨ Q) := by {
  have h1 : P → Q := h1             -- 1 [P→Q]Pr
  have tbp1 : (¬P ∨ Q) := by {
    by_cases hP : P                   -- 2 [P]PEC1
    have hQ : Q := h1 hP              -- 3 Q by Modus Ponens from 1,2
    exact Or.inr hQ                   -- 4 ¬P ∨ Q by ∨-Intro2 from 3
    have hnP : ¬P := hP               -- 5 [¬P]PEC2
    have goal2 : ¬P ∨ Q := Or.inl hP  -- 6 ¬P ∨ Q by ∨-Intro1 from 5
    exact goal2                       -- 7 ¬P ∨ Q by PEC from 2-6
  }
  exact tbp1                          -- 8 ¬P ∨ Q  by ???
}

/-
Once again, we encounter a closure statement in Lean for which no corresponding 
natural deduction operation is available (line 8). This is caused by the behavior of the 
'by_cases' tactic, which introduces two separate assumptions that are both already 
discharged in line 7.

The following example demonstrates how a proof by cases can be mimicked using 
subproofing in a highly intuitive and transparent manner.
-/

--argument form with subproofing (elimination reduced to introduction)
example  (P Q : Prop) (h1 : P → Q) : (¬P ∨ Q) := by {
  have h1 : P → Q := h1                                 -- 1 [P→Q]Pr
  have tbp_case1 : P → (¬P ∨ Q) := by {
    intro hP                                            -- 2 [P]CP
    have hQ : Q := h1 hP                                -- 3 Q by Modus Ponens from 1,2
    have goal : ¬P ∨ Q := Or.inr hQ                     -- 4 ¬P ∨ Q by ∨-Intro2 from 3
    exact goal                                          -- 5 P→(¬P∨Q) by CP from 2-4
    }
  have tbp_case2 : ¬P → (¬P ∨ Q) := by {
    intro hnP                                           -- 6 [¬P]CP
    have goal : ¬P ∨ Q := Or.inl hnP                    -- 7 ¬P ∨ Q by ∨-Intro1 from 6
    exact goal                                          -- 8 ¬P→(¬P ∨ Q) by CP from 6-7
    }
-- exact Or.elim (Classical.em P) tbp_case1 tbp_case2  -- 9 ¬P ∨ Q by PC from [P∨¬P]Th, 5,8
  exact dis_prem  (Classical.em P) tbp_case1 tbp_case2  -- 9 ¬P ∨ Q by PC from [P∨¬P]Th, 5,8 
} 
/-
Here, we have reduced the proof by cases to two conditional proofs. We can then utilize 
these subproofs by applying Lean's built-in lemma for disjunction elimination:

      Or.elim {a b c : Prop} (h : a ∨ b) (left : a → c) (right : b → c) : c

where b := ¬a. Alternatively, we can use our custom 'dis_prem' rule defined in Section 1.3.14.

Note that when hovering over "(Classical.em P)", the Lean Infoview displays the 
fundamental law of classical propositional logic:

     Classical.em (p : Prop) : p ∨ ¬p



Consequently, proving the corresponding pure formula differs from the above argument form 
only by requiring one additional structural closing layer: "exact tbp1".
-/

-- formula, subproofing
example (P Q : Prop) : (P → Q) → (¬P ∨ Q) := by {
  have tbp1 : (P → Q) → (¬P ∨ Q) := by {
    intro h1                                    -- 1 [P→Q]CP
    have tbp_case1 : P → (¬P ∨ Q) := by {
      intro hP                                  -- 2 [P] CP1
      have hQ : Q := h1 hP                      -- 3 Q by MP from 1,2
      have goal : (¬P ∨ Q) := Or.inr hQ         -- 4 ¬P∨Q by ∨-Intro2 from 3
      exact goal                                -- 5 P→(¬P∨Q) by CP1 from 2-4 
      }
    have tbp_case2 : ¬P → (¬P ∨ Q) := by {
      intro hnP                                 -- 6 [¬P] CP2
      have goal : (¬P ∨ Q) := Or.inl hnP          -- 7 ¬P∨Q by ∨-Intro1 from 6
      exact goal                                -- 8 ¬P→(¬P∨Q) by CP2 from 6-7

      }
    exact dis_prem (Classical.em P) tbp_case1 tbp_case2 -- 9 ¬P∨Q by PC from [P∨¬P]Th,5,8
  }
  exact tbp1                                    --10 (P → Q) → (¬P ∨ Q) by CP from 1-9
}

/-
However, our previous assumption that the first line of a subproof must ALWAYS repeat the 
theorem statement breaks down completely if the proof by cases is applied directly at the 
root of a pure formula. 

If the top-level structure of a formula is established via PC rather than CP, an enclosing 
'tbp1' layer cannot be constructed without causing a structural violation at the end. 
Instead, the derivation starts directly with the respective conditional case skeletons, 
with the PC meta-rule serving as the final and only top-level closure of the theorem:
-/

-- Formula, subproofing (The definitive counterexample for Top-Level PC)
example (P Q : Prop) : (P → Q) ∨ (Q → P) := by {

  have tbp_case1 : P → ((P → Q) ∨ (Q → P)) := by {
    intro hP                                      -- 1 [P]CP1
    have tbp_inner : Q → P := by {
      intro hQ                                    -- 2 [Q]CP2
      have hP : P := trivial_arg hP               -- 3 P by TA from 1
      exact hP                                    -- 4 Q→P by CP2 from 2-3
    }
    have goal : (P → Q) ∨ (Q → P) := Or.inr tbp_inner -- 5 (P→Q)∨(Q→P) by ∨-Intro2 from 4
    exact goal                                    -- 6 P → ((P → Q) ∨ (Q → P)) by CP1 from 1-5
  }

  have tbp_case2 : ¬P → ((P → Q) ∨ (Q → P)) := by {
    intro hnP                                     -- 7 [¬P]CP1
    have tbp_inner : P → Q := by {
      intro hP                                    -- 8 [P]CP2
      have cont: P ∧ ¬P := And.intro hP hnP       -- 9 P∧¬P by ∧-Intro from 7,8
      have hQ : Q := absurd hP hnP                --10 Q by ECQ from 9
      exact hQ                                    --11 P→Q from CP2 from 8-10
    }
    have goal : (P → Q) ∨ (Q → P) := Or.inl tbp_inner --12 (P→Q)∨(Q→P) by ∨-Intro1 from 11
    exact goal                                    --13 ¬P → ((P → Q) ∨ (Q → P)) by CP1 from 7-12
  }
  exact dis_prem (Classical.em P) tbp_case1 tbp_case2 -- 14 (P→Q)∨(Q→P) by PC from [P∨¬P]Th,6,13
}

/-
A closely related structural scenario occurs in proofs of equivalence (EQUI), where the 
derivation tree splits from its root into two independent, parallel implication branches. 
When attempting a strict inline subproofing approach here, a technical limitation emerges: 
Lean's strict scoping rules prohibit closing the first implication branch with an active 'exact' 
statement, as doing so would prematurely terminate the top-level proof environment and 
render the second branch unprovable.

To resolve this conflict and preserve the 1:1 symmetry with traditional natural deduction, 
we can introduce the concept of a "passive discharge" (or "discharge on hold"). Instead 
of forcing an active closure, we utilize a 'have' statement to explicitly document the 
discharge of the premise. This mechanism safely records the conditional proof step in the 
local context without collapsing the overall scope. Only in the final step is an active 
'exact' command applied to merge both passivized branches into the ultimate equivalence conclusion.

A pristine demonstration of this method can be found in Section 1.6.1, where the Equivalence 
Introduction is analyzed using the theorem 'imp_imp_comm_equi'. In that specific proof, 
lines 8 and 16 beautifully implement this passive discharge technique to maintain perfect 
isomorphism with the underlying Gentzen derivation.
-/


/-
7) Subproofing and Indirect Proofs (Proof by Contradiction)

Finally, we will demonstrate how to systematically integrate indirect proofs (IPs) 
into our subproofing framework.
-/

-- Formula, subproofing (problematic inline approach)
example (P Q : Prop) : (P → Q) → (¬P ∨ Q) := by {
  have tbp1 : (P → Q) → (¬P ∨ Q) := by {
    intro h1                                  -- 1 [P→Q]CP
    have tbp2 : (¬P ∨ Q) := by {
      by_contra hnPQ                          -- 2 [¬(¬P∨Q)]IP
      have h2 : ¬¬P ∧ ¬Q := not_or.mp hnPQ    -- 3 ¬¬P∧¬Q by [¬(p∨q)↔¬p∧¬q]Th from 2
      have hnnP : ¬¬P := h2.left              -- 4 ¬¬P by ∧-Elimination1 from 3
      have hnQ : ¬Q := h2.right               -- 5 ¬Q by ∧-Elimination2 from 3
      have hP := of_not_not hnnP              -- 6 P by DNE from 5
      have hQ : Q := h1 hP                    -- 7 Q by Modus Ponens from 1,6
      have cont : Q ∧ ¬Q := And.intro hQ hnQ  -- 8 Q∧¬Q by ∧-Intro from 5,7
      contradiction                           -- 9 Q∨¬P by IP from 2-8
    }
    exact tbp2                                --10 Q∨¬P by ???
  }
  exact tbp1                                  --11 (P → Q) → ¬P ∨ Q by CP from 1-??? 
}
/-
Once again, we encounter a closure statement in Lean for which no corresponding 
natural deduction operation is available (line 10). At the end of the 'tbp2' block, 
Lean already closes the IP internally via the 'contradiction' tactic (line 14). Consequently, 
the subsequent 'exact tbp2' command represents a redundant structural step that cannot 
be justified within a standard natural deduction derivation tree.

To establish a strict 1:1 correspondence for indirect proofs, we must encapsulate the 
IP rule into a dedicated helper theorem. Below is a tactic-based formulation of this rule:
-/

-- Tactic-style formulation of the ip_rule
theorem ip_rule {A : Prop} (B : Prop) (h: ¬A → (B ∧ ¬B)) : A := by {
  have h : ¬A → (B ∧ ¬B) := h
  by_contra hnA
  have cont : (B ∧ ¬B) := h hnA
  have hB : B := cont.left
  have hnB : ¬B := cont.right
  contradiction
}

/-
A more concise way to express this rule is in Lean's term mode, which yields the exact 
same logical behavior:
-/
/-
def ip_rule {A : Prop} (B : Prop) (h : ¬A → (B ∧ ¬B)) : A :=
  Classical.byContradiction (fun hNotA => 
    let conj := h hNotA
    conj.right conj.left
  )

By employing 'ip_rule', we can now reformulate the proof. The helper rule successfully 
binds the indirect proof to its own subproof skeleton, yielding a clean 1:1 correspondence:
-/

-- formula, subproofing with explicit IP-Workaround
example (P Q : Prop) : (P → Q) → (¬P ∨ Q) := by {
  
  have tbp1 : (P → Q) → (¬P ∨ Q) := by {
    intro h1                                        -- 1 [P→Q]CP
    
    have tbp_ip : ¬(¬P ∨ Q) → (Q ∧ ¬Q) := by {
      intro hnPQ                                    -- 2 [¬(¬P∨Q)]IP
      have h2 : ¬¬P ∧ ¬Q := not_or.mp hnPQ          -- 3 ¬¬P∧¬Q by [¬(a∨b)↔¬a∧¬b]Th from 2
      have hnnP : ¬¬P := h2.left                    -- 4 ¬¬P by ∧-Elimination from 3
      have hnQ : ¬Q := h2.right                     -- 5 ¬Q by ∧-Elimination from 3
      have hP : P := of_not_not hnnP                -- 6 P by DNE from 4
      have hQ : Q := h1 hP                          -- 7 Q by Modus Ponens from 1,6
      exact And.intro hQ hnQ                        -- 8 Q∧¬Q by ∧-Intro from 5,7
    }
    exact ip_rule Q tbp_ip                          -- 9 ¬P ∨ Q by IP from 2-8
  }
  exact tbp1                                        --10 (P → Q) → (¬P ∨ Q) by CP from 1-9
}
/-
Note on Variable Brackets:
In the declaration of 'ip_rule', the contradiction variable 'B' is written in explicit 
round brackets '(B : Prop)', while the goal variable 'A' is implicit in curly brackets '{A : Prop}'. 
This forces us to explicitly supply the specific contradiction formula (in this case, 'Q') 
as the first argument when calling 'exact ip_rule Q tbp_ip'. Lean automatically infers the 
implicit goal 'A' from the surrounding context.

Finally, we test our new IP rule against a more extreme example where the very first step of 
the proof requires negating the entire formula. This case delivers a fundamental insight:

-/

-- Formula, subproofing (The definitive counterexample for Top-Level IP)
example (P Q R : Prop) : (P → (P → ((Q ∧ R) → P))) := by {
  have tbp2 : ¬(P → (P → ((Q ∧ R) → P))) → (P ∧ ¬P) := by {
    intro h                                       -- 1 [¬(P→(P→((Q∧R)→P)))]IP
    have h1 : P ∧ ¬(P → ((Q ∧ R) → P)) := Classical.not_imp.mp h
                                                  -- 2 P∧¬(P→((Q∧R)→P)) by [¬(a→b)→a∧¬b]Th from 1 
    have hP : P := h1.left                        -- 3 P by ∧-Elimination1 from 2
    have hRest : ¬(P → ((Q ∧ R) → P)) := h1.right -- 4 ¬(P→((Q ∧ R)→P)) by ∧-Elimination2 from 2
    have h2 : P ∧ ¬((Q ∧ R) → P) := Classical.not_imp.mp hRest
                                                  -- 5 P∧¬((Q∧R)→P) by [¬(a→b)→a∧¬b]Th from 4
    have h3 : ¬((Q ∧ R) → P) := h2.right          -- 6 ¬((Q∧R)→P) by ∧-Elimination2 from 5
    have h4 : (Q ∧ R) ∧ ¬P := Classical.not_imp.mp h3 -- 7 (Q∧R)∧¬P by [¬(a→b)→a∧¬b]Th from 6
    have hnP : ¬P := h4.right                     -- 8 ¬P by ∧-Elimination2 from 7
    exact And.intro hP hnP                        -- 9 P ∧ ¬P by ∧-Intro from 3,8
  }
  exact ip_rule P tbp2                            --10 (P → (P → ((Q ∧ R) → P))) by IP from 1-9
}

/-
Note that in this scenario, we do not start with a 'tbp1' layer that repeats the initial 
theorem declaration. Lean fully accepts the proof, and the final standalone closure statement 
corresponds perfectly to derivation line 10. 

This confirms our architectural rule: whenever a logical proof tree features a classical rule 
like IP or PC at its very root rather than a constructive introduction like CP, the outer 
goal-repetition layer naturally collapses. The subproof starts directly with the rule's 
hypothetic skeleton, ensuring that your code remains structurally isomorphic to the 
underlying Gentzen derivation from the very first line.

This concludes our discussion on the Gentzen-Lean Subproofing style. We will continue with introducing additional rules in the upcoming sections and by giving example proofs in both the Gentzen-Lean Styles we have developed. In Section 1.6.5.1 we will give short introduction to a method of developing 
subproofs by a step-by-step refinement procedure: "Top-Down Structural Refinement". 
-/

---------------------------------------------------------------------------------------



--  1.6.2 (EQUI)     A → B, B → A ⊢ A ↔ B      (Equivalence Intro)

/-
The appropriate Lean lemma for formalizing (EQUI) is Iff.intro:  

    Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b

where 'mp' stands for Modus Ponens and the 'r' in 'mpr' denotes 'reverse'.

Note that according to both Iff.intro and the (EQUI) rule, it is not necessary to establish
a conjunction (A → B) ∧ (B → A) beforehand to derive A ↔ B.


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"        |Lean form "at closing step"  |Gentzen-style derivation 
have hAB : A → B := ...                |have hAB : A → B := ...      |k A → B
have hBA : B → A := ...                |have hBA : B → A := ...      |l B → A
have equi : P ↔ Q := Iff.intro hAB hBA |exact Iff.intro hAB hBA      |n A ↔ B by EQUI from k,l


We will now prove (P ∧ Q) → (P ↔ Q) using Iff.intro. For this purpose, we will apply
the following theorem formulated as an argument form:
-/

--argument form, hybrid proof
theorem and_imp_imp {P Q : Prop} (h : P ∧ Q) : (P → Q) := by {
  have hPQ : P ∧ Q := h         -- 1 [P∧Q]Pr
  by_contra hnPQ                -- 2 [¬(P→Q)]IP
  have hPnQ : P ∧ ¬Q := Classical.not_imp.mp hnPQ -- 3 P∧¬Q by [¬(a→b)↔a∧¬b]Th from 2
  have hnQ : ¬Q := hPnQ.right   -- 4 ¬Q by ∧-Elimination from 3
  have hQ : Q := hPQ.right      -- 5 Q by ∧-Elimination from 1
  have cont : Q ∧ ¬Q := And.intro hQ hnQ          -- 6 Q ∧ ¬Q by ∧-Intro from 4,5
  contradiction                 -- 7 (P→Q) by IP from 2-6 
}
/-
Next, we can easily prove the following theorem using 'and_imp_imp' and 'Iff.intro':
-/

--argument form*, hybrid proof
example {P Q : Prop} (h : P ∧ Q) : (P ↔ Q) := by {
  have hPQ : P ∧ Q := h                   -- 1 [P∧Q]Pr
  have hQP : Q ∧ P := h.symm              -- 2 Q∧P by [a∧b→b∧a]Th from 1
  have hPimpQ : P → Q := and_imp_imp hPQ  -- 3 P→Q by [(P∧Q)→(P→Q)]Th from 1
  have hQimpP : Q → P := and_imp_imp hQP  -- 4 Q→P by [(Q∧P)→(Q→P)]Th from 2
  exact Iff.intro hPimpQ hQimpP           -- 5 P↔Q by EQUI from 3,4
}

-- formula, subproofing
example {P Q : Prop} : (P ∧ Q) → (P ↔ Q) := by {
  have tbp1 : (P ∧ Q) → (P ↔ Q) := by {
    intro h1                                     -- 1 [P∧Q]CP 
    have hQP : Q ∧ P := h1.symm                  -- 2 Q∧P by MP from [a∧b→b∧a]Th and 1
    have hPimpQ : P → Q := and_imp_imp h1        -- 3 P→Q by MP from [(P∧Q)→(P→Q)]Th and 1
    have hQimpP : Q → P := and_imp_imp hQP       -- 4 Q→P by MP from [(Q∧P)→(Q→P)]Th and 2
    exact Iff.intro hPimpQ hQimpP                -- 5 P↔Q by EQUI from 3,4      
  }
  exact tbp1                                     -- 6 P ∧ Q → (P ↔ Q) by CP from 1-5
}
/-
In the hybrid Gentzen-Lean style, Lean's Iff.intro lemma can also be used to determine
the proof plan for an equivalence proof right from the start. This is done by
'apply Iff.intro', which is represented in the derivation by an unnumbered "Lean line".
-/

--formula, Gentzen-Lean hybrid style
theorem imp_imp_comm_equi {P Q R : Prop} : (P → (Q → R)) ↔ (Q → (P → R)) := by {
  -- also known as "switching premises", "commutation of premises"

  apply Iff.intro              -- Lean: goal 1: ⊢ (P → (Q → R)) → (Q → (P → R))
                               --       goal 2: ⊢ (Q → (P → R)) → (P → (Q → R))

  -- direction → 
  intro h1                    -- 1 [P→(Q→R)]CP1
  intro hQ                    -- 2 [Q]CP2
  intro hP                    -- 3 [P]CP3
  have h4 : Q → R := h1 hP    -- 4 Q→R by Modus Ponens from 1,3
  have h5 : R := h4 hQ        -- 5 R by Modus Ponens from 2,4
  exact h5                    -- 6 P→R by CP3 from 3-5
                              -- Lean: pending goal(s) silently closed
  ------------------------------------------------------------------------------
                              -- 7 Q→(P→R) by CP2 from 2-6
                              -- 8 (P → (Q → R)) → (Q → (P → R)) by CP1 from 1-7

  -- direction ←
  intro h1                    -- 9 [Q→(P→R)]CP1
  intro hP                    --10 [P]CP2
  intro hQ                    --11 [Q]CP3
  have h12 : P → R := h1 hQ   --12 P→R by Modus Ponens from 9,11
  have h13 : R := h12 hP      --13 R by Modus Ponens from 10, 12
  exact h13                   --14 Q → R by CP3 from 11-13
                              -- Lean: pending goal(s) silently closed
  ------------------------------------------------------------------------------
                              --15 (P → (Q → R)) by CP2 from 10-14
                              --16 (Q → (P → R)) → (P → (Q → R)) by CP1 from 9-15
                              --17 (P → (Q → R)) ↔ (Q → (P → R)) by EQUI from 8,16
}


theorem imp_imp_comm_equi' {P Q R : Prop} : (P → (Q → R)) ↔ (Q → (P → R)) := by {

  have tbp2 : (P → (Q → R)) → (Q → (P → R)) := by {
    intro h1                              -- 1 [P→(Q→R)]CP1
    have tbp3 : (Q → (P → R)) := by {
      intro hQ                            -- 2 [Q]CP2
      have tbp4 : (P → R) := by {
        intro hP                          -- 3 [P]CP3
        have hQR : Q → R := h1 hP         -- 4 Q→R by Modus Ponens from 1,3
        exact hQR hQ                      -- 5 R by Modus Ponens from 2,4
      }
      exact tbp4                          -- 6 P→R by CP3 from 3-5  
    }
    exact tbp3                            -- 7 Q→(P→R) by CP2 from 2-6    
  }
  have goal1 : (P → (Q → R)) → (Q → (P → R)) := tbp2
                           -- 8 (P → (Q → R)) → (Q → (P → R)) by CP1 from 1-7

  have tbp2' : (Q → (P → R)) → (P → (Q → R)) := by {
    intro h1                              -- 9 [Q→(P→R)]CP1
    have tbp3 : (P → (Q → R)) := by {
      intro hP                            --10 [P]CP2
      have tbp4 : (Q → R) := by {
        intro hQ                          --11 [Q]CP3
        have hPR : P → R := h1 hQ         --12 P→R by Modus Ponens from 9,11
        exact hPR hP                      --13 R by Modus Ponens from 10,12             
      }
      exact tbp4                          --14 Q → R by CP3 from 11-13
    }
    exact tbp3                            --15 (P → (Q → R)) by CP2 from 10-14
  }
  have goal2 : (Q → (P → R)) → (P → (Q → R)) := tbp2'
                           --16 (Q → (P → R)) → (P → (Q → R)) by CP1 from 9-15

  exact Iff.intro goal1 goal2             -- 17 P→(Q→R) ↔ Q→(P→R) by EQUI from 8,16
}

-------------------------------------------------------------------------------

--1.6.3 (EQUI∧) (A → B) ∧ (B → A) ⊢ A ↔ B   (Equivalence Intro∧)
/-

For those who prefer a rule closer in spirit to the traditional definition:

      A ↔ B := A → B ∧ B → A  (Def'↔')

it might be desirable to prove equivalences according to the more explicit rule:

    (EQUI∧) A → B ∧ B → A ⊢ A ↔ B.

Since Lean does not feature an exact built-in lemma matching this formulation, 
we will formalize (EQUI∧) ourselves by introducing a custom theorem:
-/ 

--  (EQUI∧)
theorem iff_intro_rule {A B : Prop} (h : (A → B) ∧ (B → A)) : A ↔ B :=
  Iff.intro h.left h.right

/-
As an example, we can now reformulate our argument form* proof from the previous section.
By utilizing our more explicit "iff_intro_rule", we make the underlying conjunction 
of (Def'↔') visible once again:
-/

--argument form, hybrid
example {P Q : Prop} (h : P ∧ Q) : (P ↔ Q) := by {
  have hPQ : P ∧ Q := h                   -- 1 [P∧Q]Pr
  have hQP : Q ∧ P := h.symm              -- 2 Q∧P by [a∧b→b∧a]Th from 1
  have hPimpQ : P → Q := and_imp_imp hPQ  -- 3 P→Q by [(P∧Q)→(P→Q)]Th from 1
  have hQimpP : Q → P := and_imp_imp hQP  -- 4 Q→P by [(Q∧P)→(Q→P)]Th from 2
  have conj : (P → Q) ∧ (Q → P) := And.intro hPimpQ hQimpP  -- 5 (P→Q)∧(Q→P) by ∧-Intro from 3,4 
  exact iff_intro_rule conj               -- 6 P↔Q by EQUI∧ from 5
}

-- formula, subproofing
example {P Q : Prop} : (P ∧ Q) → (P ↔ Q) := by {
  have tbp1 : (P ∧ Q) → (P ↔ Q) := by {
    intro hPQ                                -- 1 [P∧Q]CP
    have hQP : Q ∧ P := hPQ.symm             -- 2 Q∧P by [a∧b→b∧a]Th and 1                  
    have hPimpQ : P → Q := and_imp_imp hPQ   -- 3 P→Q by [(P∧Q)→(P→Q)]Th and 1        
    have hQimpP : Q → P := and_imp_imp hQP   -- 4 Q→P by [(Q∧P)→(Q→P)]Th and 2       
    have goal : (P → Q) ∧ (Q → P) := And.intro hPimpQ hQimpP  -- 5 (P→Q)∧(Q→P) by ∧-Intro from 3,4
    exact iff_intro_rule goal                -- 6 P ↔ Q by EQUI∧ from 5
  }
  exact tbp1                                 -- 7 (P ∧ Q) → (P ↔ Q) by CP from 1-6
}


/-
Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"       |Lean form "at closing step"        |Gentzen-style derivation 
have h : (A → B) ∧ (B → A) := ...     |have h : (A → B) ∧ (B → A) := ...  |k (A → B) ∧ (B → A)
have equi : P ↔ Q := iff_intro_rule h |exact iff_intro_rule h             |n A ↔ B by EQUI∧ from k
-/

------------------------------------------------------------------------------------------


-- 1.6.4 (EQUE1) A ↔ B ⊢ A → B                   (Equivalence Elimination 1)

/-
In Lean, the lemma 'Iff.mp' corresponds directly to the (EQUE1) rule:

    Iff.mp {a b : Prop} (self : a ↔ b) : a → b


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"       |Lean form "at closing step"     |Gentzen-style derivation 
have h : (A ↔ B) := ...               |have h : (A ↔ B) := ...         |k (A ↔ B)
have hPimpQ : A → B := Iff.mp h       |exact Iff.mp h                  |n A → B by EQUE1 from k


We can apply Iff.mp twice to prove the following example:
-/

--formula, hybrid proof
example {P Q R : Prop} : ((P ↔ Q) ∨ (R ↔ Q)) → ((P ∧ R) → Q) := by {
  intro h_disj                        -- 1 [(P↔Q)∨(R↔Q)]CP1
  intro h2                            -- 2 [P∧R]CP2
  rcases h_disj with hPQ | hRQ        -- Lean: PC with [P↔Q]PC1 and [R↔Q]PC2
  have hPQ : (P ↔ Q) := hPQ           -- 3 [P↔Q]PC1
  have hPQmp : (P → Q) := Iff.mp hPQ  -- 4 P→Q by EQUE1 from 3
  have hP : P := h2.left              -- 5 P from ∧-Elimination from 2
  exact hPQmp hP                      -- 6 Q by Modus Ponens from 4,5
  have hRQ : R ↔ Q := hRQ             -- 7 [R↔Q]PC2
  have hRQmp : R → Q := Iff.mp hRQ    -- 8 R→Q by EQUE1 from 7
  have hR : R := h2.right             -- 9 R by ∧-Elimination from 2
  exact hRQmp hR                      --10 Q by Modus Ponens from 8,9
                                      -- Lean: pending goal(s) silently closed
  -----------------------------------------------------------------------------
                                      --11 Q by PC from 1, 3-6, 7-10
                                      --12 ((P ∧ R) → Q) by CP2 from 2-11
                                      --13 ((P ↔ Q) ∨ (R ↔ Q)) → ((P ∧ R) → Q) by CP1 from 1-12
}

-- formula, subproofing
example {P Q R : Prop} : ((P ↔ Q) ∨ (R ↔ Q)) → ((P ∧ R) → Q) := by {
  have tbp1 : ((P ↔ Q) ∨ (R ↔ Q)) → ((P ∧ R) → Q) := by {
    intro h_disj                            -- 1 [(P↔Q)∨(R↔Q)]CP1
    
    have tbp2 : ((P ∧ R) → Q) := by {
      intro hPR                             -- 2 [P∧R]CP2
      
      have tbp_case1 : (P ↔ Q) → Q := by {
        intro hPQ                           -- 3 [P↔Q]PC1
        have hPQmp : (P → Q) := Iff.mp hPQ  -- 4 P→Q by EQUE1 from 3
        have hP : P := hPR.left             -- 5 P from ∧-Elimination from 2
        exact hPQmp hP                      -- 6 Q by Modus Ponens from 4,5
      }
      
      have tbp_case2 : (R ↔ Q) → Q := by {
        intro hRQ                           -- 7 [R↔Q]PC2
        have hRQmp : R → Q := Iff.mp hRQ    -- 8 R→Q by EQUE1 from 7
        have hR : R := hPR.right            -- 9 R by ∧-Elimination from 2
        exact hRQmp hR                      -- 10 Q by Modus Ponens from 8,9
      }

      exact Or.elim h_disj tbp_case1 tbp_case2-- 11 Q by PC from 1, 3-6, 7-10
    } 
    exact tbp2                              -- 12 ((P ∧ R) → Q) by CP2 from 2-11
  }
  exact tbp1                                -- 13 ((P ↔ Q) ∨ (R ↔ Q)) → ((P ∧ R) → Q) by CP1 from 1-12
}


-----------------------------------------------------------------------------------------------


-- 1.6.5 (EQUE2) A ↔ B ⊢ B → A                   (Equivalence Elimination 2)

/-
In Lean, the lemma 'Iff.mpr' corresponds directly to the (EQUE2) rule:

    Iff.mpr {a b : Prop} (self : a ↔ b) : b → a


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"       |Lean form "at closing step"     |Gentzen-style derivation 
have h : (A ↔ B) := ...               |have h : (A ↔ B) := ...         |k (A ↔ B) 
have hBimpA : B → A := Iff.mpr h      |exact Iff.mpr h                 |n B → A by EQUE2 from k


We can apply Iff.mpr to prove the following example:
-/

--argument form, hybrid proof
example {P Q R : Prop} (h1 : Q ↔ P) (h2 : Q → R) : P → R := by {
  have h1 : Q ↔ P := h1           -- 1 [Q↔P]Pr
  have h2 : Q → R := h2           -- 2 [Q→R]Pr
  intro hP                        -- 3 [P]CP
  have hPQ : P → Q := Iff.mpr h1  -- 4 P→Q by EQUE2 from 1
  have hQ : Q := hPQ hP           -- 5 Q by Modus Ponens from 3,4
  have hR : R := h2 hQ            -- 6 R by Modus Ponens from 2,5
  exact hR                        -- 7 P → R by CP from 3-6 
}

--argument form, subproofing
example {P Q R : Prop} (h1 : Q ↔ P) (h2 : Q → R) : P → R := by {
  have h1 : Q ↔ P := h1           -- 1 [Q↔P]Pr
  have h2 : Q → R := h2           -- 2 [Q→R]Pr
  have tbp : P → R := by {
    intro hP                      -- 3 [P]CP
    have hPQ : P → Q := Iff.mpr h1-- 4 P→Q by EQUE2 from 1
    have hQ : Q := hPQ hP         -- 5 Q by Modus Ponens from 3,4
    exact h2 hQ                   -- 6 R by Modus Ponens from 2,5 
  }
  exact tbp                       -- 7 P→R by CP from 3-6
}
/-
We conclude the sections on (EQUE1) and (EQUE2) by presenting a theorem that features 
three equivalence symbols. This serves as an ideal benchmark for examining how deep 
structural branchings affect goal tracking.
-/

--formula, Gentzen-Lean hybrid style
theorem equi_negation_shift {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by {
-- known under the name "Negation Shift of Equivalence"
  
  apply Iff.intro                           -- Lean: goal 1: ⊢ (¬P ↔ Q) → (P ↔ ¬Q)
                                            --       goal 2: ⊢ (P ↔ ¬Q) → (¬P ↔ Q)

  -- direction →
  intro h1                                  -- 1 [¬P↔Q]CP1
  have hQnP : Q → ¬P := Iff.mpr h1          -- 2 Q→¬P by EQUE2 from 1
  
  apply Iff.intro                           -- Lean: goal 1: ⊢ P → ¬Q
                                            --       goal 2: ⊢ ¬Q → P
  intro hP                                  -- 3 [P]CP2
  have hnnP : ¬¬P := not_not_intro hP       -- 4 ¬¬P by DNI from 3  
                            
  have final1 : ¬Q := mt hQnP hnnP          -- 5 ¬Q by Modus Tollens from 2,4
  exact final1                              -- 6 (P → ¬Q) by CP2 from 3-5

  intro h2                                  -- 7 [¬Q]CP3
  have hnPQ : ¬P → Q := Iff.mp h1           -- 8 ¬P→Q by EQUE1 from 1
  have hnnP : ¬¬P := mt hnPQ h2             -- 9 ¬¬P by Modus Tollens from 7,8
  have hP : P := of_not_not hnnP            --10 P by DNE from 9
  exact hP                                  --11 (¬Q → P) by CP3 from 7-10
                                            -- Lean: pending goal(s) silently closed
  -------------------------------------------------------------------------------------
                                            --12 (P ↔ ¬Q) by EQUI from 6,11
                                            --13 (¬P ↔ Q) → (P ↔ ¬Q) by CP1 from 1-12
  
  -- direction ←
  intro h1                                  --14 [P↔¬Q]CP1
--  rcases h1 with ⟨hP, hQ⟩                   --15 P → ¬Q, ¬Q → P by ∧-Eliminations from 14
  have hnQP : ¬Q → P := Iff.mpr h1          --15 ¬Q → P by EQUE2 from 14 
  
  apply Iff.intro                           -- Lean: goal 1: ⊢ ¬P → Q
                                            --       goal 2: ⊢ Q → ¬P

  intro h3                                  --16  [¬P]CP2
  have hnnQ : ¬¬Q := mt hnQP h3             --17 ¬¬Q by Modus Tollens from 15, 16
  have hQ : Q := of_not_not hnnQ            --18 Q by DNE from 17 
  exact hQ                                  --19 ¬P → Q by CP2 from 16-18

  intro h3                                  --20 [Q]CP3 
  have hnnQ : ¬¬Q := not_not_intro h3       --21 ¬¬Q by DNI from 20
  have hPnQ : P → ¬Q := Iff.mp h1           --22 P→¬Q by EQUE1 from 14
  have hP : ¬P := mt hPnQ hnnQ              --23 ¬P by Modus Tollens from 21, 22
  exact hP                                  --24 Q → ¬P by CP3 from 20-23
                                            -- Lean: pending goal(s) silently closed
  -------------------------------------------------------------------------------------
                                            --25 (¬P ↔ Q) by EQUI from 19,24
                                            --26 (P ↔ ¬Q) → (¬P ↔ Q) by CP1 from 14-25
                                            --27 (¬P ↔ Q) ↔ (P ↔ ¬Q) by EQUI from 13,26
}
/-
Remark: Above, the outcommented line 15, 'rcases h1 with ⟨hP, hQ⟩', represents an alternative
method to draw separate directions from an equivalence. To infer only one direction, one
can use 'rcases h1 with ⟨_, hQ⟩' or 'rcases h1 with ⟨hP, _⟩'.
(Cf. Section 1.2.5.1 Excursion: ∧-Component Extraction)
-/

/-
-- 1.6.5.1  Top-Down Structural Refinement: Developing Complex Subproofs Inkrementally

An exceptionally helpful method for constructing and understanding larger proofs in the 
Gentzen-Lean subproofing style is to first map out the structural skeleton and then 
fill it with logical content (or nested substructures) step by step. 

We begin by examining the root of the derivation tree to determine the overall top-level architecture. 
In the present example, we target the Negation Shift of Equivalence: (¬P ↔ Q) ↔ (P ↔ ¬Q). 
We can immediately see that the final equivalence will be established via Equivalence Introduction (EQUI). 
To achieve this, we must have both directions, namely (¬P ↔ Q) → (P ↔ ¬Q) and (P ↔ ¬Q) → (¬P ↔ Q), 
already proven. To formulate this top-level skeleton while leaving the inner components open, 
we can use Lean's 'sorry' keyword to temporarily bypass incomplete sections of the proof:
-/

-- Step 1: Mapping out the Top-Level Equivalence Branches
example {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by {

  have tbp1 : (¬P ↔ Q) → (P ↔ ¬Q) := by {
    sorry
  }
  have tbp2 : (P ↔ ¬Q) → (¬P ↔ Q) := by {
    sorry
  }
  exact Iff.intro tbp1 tbp2
}

/-
Utilizing the interactive feedback of the Lean Infoview and mouse-over tooltips is vital 
for detecting syntax errors. However, maintaining critical logical thinking remains paramount, 
as the next —initially tempting— alternative skeleton demonstrates:
-/

-- Counterexample: Attempting an explicit top-level goal repetition
example {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by {
  have tbp : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by {

    have tbp1 : (¬P ↔ Q) → (P ↔ ¬Q)  := by {
    sorry
    }
    have tbp2 : (P ↔ ¬Q) → (¬P ↔ Q) := by {
    sorry
    }
    exact Iff.intro tbp1 tbp2
  }
  exact tbp
}
/-
As critical observers, we immediately detect that wrapping the entire equivalence in an 
outer 'have tbp' layer produces an illegal line-doubling on the derivation side during 
the closing steps. Consequently, we discard this bloated alternative and return to our 
original, structurally clean top-level skeleton.

Next, we move up one step in our derivation tree, which now features two independent edges 
leading down to the root. At the top of these edges, we face the conditional goals 
(¬P ↔ Q) → (P ↔ ¬Q) and (P ↔ ¬Q) → (¬P ↔ Q). We apply Conditional Proof (CP) to split 
the first main branch, introducing its respective assumptions and inner skeletons:
-/

-- Step 2: Refining the Forward Implication Branch
example {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by {

  have tbp1 : (¬P ↔ Q) → (P ↔ ¬Q) := by {
    intro h                                 -- [¬P↔Q]CP1
    have tbp1_1 : (P → ¬Q) := by {
      intro hP                              -- [P]CP2
      sorry
    }
    have tbp1_2 : ¬Q → P := by {
      intro hnQ                             -- [¬Q]CP3
      sorry
    }
    exact Iff.intro tbp1_1 tbp1_2
  }
  have tbp2 : (P ↔ ¬Q) → (¬P ↔ Q) := by {
    sorry
  }
  exact Iff.intro tbp1 tbp2

}
/-
Following the exact same structural blueprint, we apply Conditional Proof to the 
backward implication branch on the other side of the tree:
-/

-- Step 3: Completing the Entire Multi-Layered Subproof Skeleton
example {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by {

  have tbp1 : (¬P ↔ Q) → (P ↔ ¬Q) := by {
    intro h                                 -- [¬P↔Q]CP1
    have tbp1_1 : (P → ¬Q) := by {
      intro hP                              -- [P]CP2
      sorry
    }
    have tbp1_2 : ¬Q → P := by {
      intro hnQ                             -- [¬Q]CP3
      sorry
    }
    exact Iff.intro tbp1_1 tbp1_2
  }
  have tbp2 : (P ↔ ¬Q) → (¬P ↔ Q) := by {
    intro h                                 -- [(P↔¬Q]CP1
    have tbp2_1 : (¬P → Q) := by {
      intro hnP                             -- [¬P]CP2
      sorry
    }
    have tbp2_2 : Q → ¬P := by {
      intro hQ                              -- [Q]CP3
      sorry
    }
    exact Iff.intro tbp2_1 tbp2_2
  }
  exact Iff.intro tbp1 tbp2
}
/-
Finally, looking at our fully fleshed-out skeleton, we notice that every necessary 
hypothetical assumption has been successfully introduced. With the architecture firmly 
established, we can safely proceed to fill in the remaining logical gaps with atomic 
deductions and rules:
-/

theorem equi_negation_shift' {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by {

  have tbp1 : (¬P ↔ Q) → (P ↔ ¬Q) := by {
    intro h1                                 -- 1 [¬P↔Q]CP1
    
    have tbp1_1 : (P → ¬Q) := by {
      intro hP                               -- 2 [P]CP2
      have hQnP : Q → ¬P := Iff.mpr h1       -- 3 Q→¬P by EQUE2 from 1       
      have hnnP : ¬¬P := not_not_intro hP    -- 4 ¬¬P by DNI from 2
      have hnQ : ¬Q := mt hQnP hnnP          -- 5 ¬Q by Modus Tollens from 3,4
      exact hnQ                              -- 6 (P → ¬Q) by CP2 from 3-5
    }
    have tbp1_2 : ¬Q → P := by {
      intro h2                                -- 7 [¬Q]CP3
      have hnPQ : ¬P → Q := Iff.mp h1         -- 8 ¬P→Q by EQUE1 from 1
      have hnnP : ¬¬P := mt hnPQ h2           -- 9 ¬¬P by Modus Tollens from 7,8
      have hP : P := of_not_not hnnP          --10 P by DNE from 9
      exact hP                                --11 (¬Q → P) by CP3 from 7-10
    }

    have goal1 : (P ↔ ¬Q) := Iff.intro tbp1_1 tbp1_2 --12 (P ↔ ¬Q) by EQUI from 6,11
    exact goal1                               --13 (¬P ↔ Q) → (P ↔ ¬Q) by CP1 from 1-12
  }

  have tbp2 : (P ↔ ¬Q) → (¬P ↔ Q) := by {
    intro h                                   --14 [P↔¬Q]CP1
    
    have tbp2_1 : (¬P → Q) := by {
      intro hnP                               --15 [¬P]CP2
      have hnQP : ¬Q → P := Iff.mpr h         --16 ¬Q → P by EQUE2 from 14
      have hnnQ : ¬¬Q := mt hnQP hnP          --17 ¬¬Q by Modus Tollens from 15, 16
      have hQ : Q := of_not_not hnnQ          --18 Q by DNE from 17 
      exact hQ                                --19 (¬P → Q) by CP2 from 15-18
    }
    have tbp2_2 : Q → ¬P := by {
      intro hQ                                --20 [Q]CP3
      have hnnQ : ¬¬Q := not_not_intro hQ     --21 ¬¬Q by DNI from 20
      have hPnQ : P → ¬Q := Iff.mp h          --22 P→¬Q by EQUE1 from 14
      have hnP : ¬P := mt hPnQ hnnQ           --23 ¬P by Modus Tollens from 21, 22
      exact hnP                               --24 (Q → ¬P) by CP3 from 20-23
    }
    have goal2 : (¬P ↔ Q) := Iff.intro tbp2_1 tbp2_2 --25 (¬P ↔ Q) by EQUI from 19,24 
    exact goal2                               --26 (P ↔ ¬Q) → (¬P ↔ Q) by CP1 from 14-25
  }
  exact Iff.intro tbp1 tbp2                   --27 (¬P ↔ Q) → (P ↔ ¬Q) by EQUI from 13,26
}



---------------------------------------------------------------------------------
-- 1.6.6 Meta-Rules Addendum: The Substitution Rule (Substitution of Equivalents)
/-
It is now time to introduce another meta-rule that has not been mentioned before: 
the Substitution of Equivalents (SUBST).

    If B is a subformula of a derivable formula A (denoted as A[B]),
    and if B ↔ C is also derivable,
    then A[C] is derivable, provided that B is uniformly substituted by C within A.

In Lean, an intuitive and powerful method for applying the (SUBST) rule is provided 
by the rewrite tactic 'rw'.

A concrete example illustrating this approach is presented in the next section.
-/

---------------------------------------------------------------------------------



-- 1.6.7     (EQUS)  (A ↔ B) ⊢ (B ↔ A)               (Symmetry of Equivalence)
/-
In Lean, the lemma 'Iff.symm' corresponds directly to the (EQUS) rule:

    Iff.symm {a b : Prop} (h : a ↔ b) : b ↔ a


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"       |Lean form "at closing step"      |Gentzen-style derivation 
have h : A ↔ B := ...                 |have h : A ↔ B := ...            |k A ↔ B
have h1 : B ↔ A := Iff.symm h         |exact Iff.symm h                 |n B ↔ A by EQUS from k

--Examples
-/

--formula, hybrid
example {P Q R S : Prop} : ((R ∨ S) ↔ (P ∧ Q)) → ((Q ∧ P) ↔ (S ∨ R)) := by {
  intro h1                                            -- 1 [R∨S↔P∧Q]CP
  have h1' : (P ∧ Q) ↔ (R ∨ S) := Iff.symm h1         -- 2 (P∧Q)↔(R∨S) by EQUS from 1
  have h1'' : (Q ∧ P) ↔ (S ∨ R) := by rw [And.comm, Or.comm, h1']
                                    -- 3 (Q∧P)↔(S∨R) by 2 SUBST from [a∧b↔b∧a]Th, [a∨b↔b∨a]Th, 2
  exact h1''                        -- 4 ((R ∨ S) ↔ (P ∧ Q)) → ((Q ∧ P) ↔ (S ∨ R)) by CP from 1
}
/-
A cleaner version is presented below, where the rewrite steps are performed separately:
-/

--formula, hybrid
example {P Q R S : Prop} : ((R ∨ S) ↔ (P ∧ Q)) → ((Q ∧ P) ↔ (S ∨ R)) := by {
  intro h1                                             -- 1 [R∨S↔P∧Q]CP
  have h1' : (P ∧ Q) ↔ (R ∨ S) := Iff.symm h1          -- 2 (P∧Q)↔(R∨S) by EQUS from 1
  have h2 : (Q ∧ P) ↔ (R ∨ S) := by rw [And.comm, h1'] -- 3 (Q∧P)↔(R∨S) by SUBST from [a∧b↔b∧a]Th, 2
  have h3 : (Q ∧ P) ↔ (S ∨ R) := by rw [Or.comm, h2]   -- 4 (Q∧P)↔(S∨R) by SUBST from [a∨b↔b∨a]Th, 3 
  exact h3                          -- 5 ((R ∨ S) ↔ (P ∧ Q)) → ((Q ∧ P) ↔ (S ∨ R)) by CP from 1-4
}

--formula, subproofing ("take the long way home" version)
example {P Q R S : Prop} : ((R ∨ S) ↔ (P ∧ Q)) → ((Q ∧ P) ↔ (S ∨ R)) := by {
  have tbp1 : ((R ∨ S) ↔ (P ∧ Q)) → ((Q ∧ P) ↔ (S ∨ R)) := by {
    intro h1                                    -- 1 [R∨S↔P∧Q]CP
    
    have tbp2 : ((Q ∧ P) → (S ∨ R)) := by {
      intro h3                                  -- 2 [Q∧P]CP
      have h3_symm : (P ∧ Q) := h3.symm         -- 3 P∧Q by [a∧b→b∧a]Th from 2
      have h4 : (P ∧ Q) → (R ∨ S) := Iff.mpr h1 -- 4 P∧Q→R∨S by EQUE2 from 1
      have h5 : (R ∨ S) := h4 h3_symm           -- 5 R∨S by Modus Ponens from 3,4
      have h6 : (S ∨ R) := h5.symm              -- 6 S∨R by [a∨b↔b∨a]Th from 5
      exact h6                                  -- 7 (Q∧P)→(S∨R) by CP from 2-6
    }
    
    have tbp3 : ((S ∨ R) → (Q ∧ P)) := by {
      intro h3                                  -- 8 [S∨R]CP
      have h3_symm : (R ∨ S) := h3.symm         -- 9 R∨S by [a∨b↔b∨a]Th from 8 
      have h4 : (R ∨ S) → (P ∧ Q) := Iff.mp h1  --10 (R∨S)→(P∧Q) by EQUE1 from 1
      have h5 : (P ∧ Q) := h4 h3_symm           --11 P∧Q by Modus Ponens from 9,10
      have h6 : (Q ∧ P) := h5.symm              --12 Q∧P by [a∧b→b∧a]Th from 11
      exact h6                                  --13 (S ∨ R) → (Q ∧ P) by CP from 8-12
    }
    exact Iff.intro tbp2 tbp3                   --14 (Q ∧ P) ↔ (S ∨ R) by EQUI from 2-13
  }
  exact tbp1                             --15 (R ∨ S ↔ P ∧ Q) → (Q ∧ P ↔ S ∨ R) by CP from 1-14
}
---------------------------------------------------------------------------------


-- 1.6.8     Proofs by Equivalence Transformations

/-
This proof is special and shows 3 important things:
  1) How to start a proof with a theorem (Th1).
  2) How to insert a conjunction of theorems somewhere in the middle of a proof (nn).
  3) How to apply Congruence Rules** in Lean (Tth2, Th3)
-/

--Proof by Equivalence Transformations
theorem and_equi_or_ {P Q : Prop} : (P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := by {
  have th1 : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by exact not_and_or
  -- 1 [¬(P∧Q)↔¬P∨¬Q]Th1
  -- Remark: Now we apply negation on both sides of "↔" of Th1:
  have th2 : ¬¬(P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := Iff.not th1
  -- 2 ¬¬(P∧Q)↔¬(¬P∨¬Q) by Modus Ponens from [(a↔b)↔(¬a↔¬b)]Th2, 1
  have nn : (P ∧ Q) ↔ ¬¬(P ∧ Q) := by exact Iff.intro not_not_intro of_not_not
  -- 3  (P∧Q) ↔ ¬¬(P∧Q) by ∧-Intro from [A→¬¬A]Th3, [¬¬A→A]Th4 *
  have th3 : (P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := Iff.trans nn th2
  -- 4 (P∧Q) ↔ ¬(¬P∨¬Q) by [(A↔B)∧(B↔C)→(A↔C)]Th5 from 3,2
  exact th3
}

/-
* Remark: In line 3 we use anonymous constructors ⟨...⟩, introduced in Section 1.3.9.
          Lean interprets the conjunction as equivalence. Our usual method of representing
          'nn' works, too: "by exact Iff.intro not_not_intro of_not_not"

** Remark on Congruence Rules: Equivalence is congruent under logical operators:

                                A ↔ B ⇒ f(A) ↔ f(B)

          Hence, if (A ↔ B), then also (¬A ↔ ¬B), (A∧C ↔ B∧C), (A∨C ↔ B∨C), (A→C ↔ B→C)

Implemented in Lean:  Iff.not : (A ↔ B) → (¬A ↔ ¬B)
                      Iff.and : (h₁ : A ↔ B) (h₂ : C ↔ D) :  (A ∧ C) ↔ (B ∧ D)
                      Iff.or  : (h₁ : A ↔ B) (h₂ : C ↔ D) : (A ∨ C) ↔ (B ∨ D)
                      Iff.imp : (h₁ : A ↔ B) (h₂ : C ↔ D) : (A → C) ↔ (B → D)
-/




end propositional_logic