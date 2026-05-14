-- Tested on live.lean-lang.org
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
open Classical


/-!
# THE GENTZEN–LEAN PROVING STYLE IN MATHEMATICAL LOGIC



## Abstract
**Introduction** The objective of this work is to bridge the gap between traditional
  Gentzen-style logical derivations and interactive theorem proving in Lean 4 tactic
  mode by exploring the possibility of a strict 1:1 mapping of the two formalisms.
  
**Success of Local Rules:** Success of Local Rules: Standard linear inference rules -
  such as Modus Ponens (MP), Modus Tollens (MT), Disjunctive Syllogisms (DS1/DS2), and
  Conjunction rules (∧E/∧I) — map perfectly onto explicit Lean expressions. Using "have"
  structures for intermediate steps preserves exact granularity. To isolate the behavior
  of these basic rules, our analysis is restricted to derivations containing at most a
  single application of any meta-rule (IP, CP, or PC). Even within this scope, a notable
  exception is the disjunction rule (Proof by Cases, PC: A ∨ B, A → C, B → C ⊢ C), for 
  which we provide a counterexample that cannot be represented in a 1:1 fashion.
  Consequently, both this limitation and the challenges of nested meta-rules lead us 
  directly to the problem of *Implicit Structural Closure*.

**The Limit of Implicit Structural Closure:** Lean’s proof engine operates on a
  goal-driven mechanism. When a final target type is synthesized, closing commands like
  exact or contradiction immediately terminate subgoals internally. This automation
  introduces a structural boundary: Lean obscures the distinction between constructing
  the final proposition and discharging the surrounding meta-rule context (e.g., CP or IP).

**Branching and Asymmetry Boundaries:** The absolute 1:1 mapping encounters a 
  conceptual bottleneck in rules that trigger structural splits (such as Disjunction
  Elimination via `rcases` or `by_cases`). Forcing a strict line-by-line derivation
  creates a structural asymmetry, wherein the tactic command must simultaneously serve
  as both the structural announcement and the implicit, immediate assumption of the first
  branch.

**The Hybrid Derivation Paradigm:** To escape artificial proof constructs while maintaining
  absolute explicitness, we propose a *Hybrid Gentzen-Lean Style*. By embedding unnumbered,
  metadata-rich Lean comments alongside the strictly numbered Gentzen sequence, the proof
  architecture remains readable for human logicians and transparent for machine analysis. This 
  coexistence preserves the deductive linearity of natural deduction without hiding Lean’s
  internal goal transformations.
-/

/-
-------------------------------
C O N T E N T S
-------------------------------

1       Propositional Logic
1.1     Introduction
1.2     The List of Rules
1.3     Basic Rules
1.4     Meta-Rules
-------------------------------
1.5     Preliminary Conclusion
-------------------------------
1.6     More Derived Rules
-/

-- 1 Propositional Logic

-- 1.1 Introduction
/-
Methodological outline:
In what follows, we demonstrate that the rules of a specific Gentzen-style
natural deduction system can, in their concrete applications within derivations,
be mapped in a near one-to-one manner onto Lean proofs written in tactic mode.

We deliberately abstract away from Lean’s internal proof construction and focus
instead on extensional correspondence: Lean steps and derivation steps are compared
in terms of the results they produce and the transformations they perform. All
subsequent comparisons are to be understood in this sense.

In the few cases where this direct correspondence breaks down, we consider three
possible responses:
1) to preserve the 1:1 correspondence by suitable reformulation,
2) to abandon it where necessary, or
3) to adopt a hybrid derivation style, i.e. a derivation that combines
   numbered lines with additional, unnumbered Lean comments.

In all three cases, the result is a Lean proof annotated by a structure
that closely mirrors a classical derivation.

Example (perfect 1:1)
('CP' for 'Conditional Proof'):
-/

example {P Q : Prop} : (P ∧ Q) → (Q ∧ P) := by {
  intro h                            -- 1 [P∧Q]CP
  have hP : P := h.left              -- 2 P by ∧-Elimination1 from 1
  have hQ : Q := h.right             -- 3 Q by ∧-Elimination2 from 1
  have h1 : Q ∧ P := And.intro hQ hP -- 4 Q ∧ P by ∧-Intro from 2,3
  exact h1                           -- 5 (P ∧ Q) → (Q ∧ P) by CP from 1–4
}

/-
Advantages of this "fusion" of Gentzen-style derivations and Lean proofs include:

1) Improved readability of Lean code for humans, especially for specialists
   in modern symbolic logic.
2) Easier entry into Lean, since both the number and the type of tactics are
   deliberately restricted and aligned with familiar deduction rules.
3) Direct mutual verification between formal Lean proofs and formal
   derivations (assuming either the Lean proof or the derivation is trusted);
   potential for automation.
4) Hybrid derivations remain usable in metatheoretical contexts, since
   non-numbered Lean comments can be removed without affecting structure;
   these comments may also be helpful information in automated creation of
   Lean proofs from derivations
5) Most importantly, the seemingly pedantic step-by-step derivation style
   may prove essential for future developments in AI-assisted reasoning systems.

Beyond pedagogical considerations, the Gentzen–Lean style is relevant because
it enforces a highly granular and explicitly structured form of reasoning.
Such structure is not only beneficial for human readability but also aligns well
with the requirements of machine-assisted proof analysis and transformation.

In particular, step-by-step derivations with clearly identifiable rule applications
provide a natural interface for automation, proof checking, and proof search. They
make implicit reasoning explicit and thereby reduce the gap between informal
mathematical arguments and fully formalized proofs.

This suggests that seemingly “pedantic” derivation styles may play a crucial role
in future developments of AI-assisted reasoning systems, where transparency,
traceability, and modularity of proofs are essential.
-/

/-
-- 1.2 The List of Rules

We begin with a selection of basic inference rules that we consider
particularly convenient and useful in practice. These rules are not
necessarily logically independent; rather, they are chosen for their
ubiquity in standard derivations.

At this stage, we deliberately ignore the distinction between classical
and intuitionistic reasoning as reflected in Lean.
Although Lean is based on an intuitionistic foundation, classical
reasoning can be enabled by importing classical axioms via

  open Classical

at the beginning of a `.lean` file. This allows us to work uniformly
with both classical and intuitionistic principles.

It is not our goal to develop a system from scratch. We allow ourselves
to make use of theorems not already proven thereby relaxing the usual
requirement of a strict derivation order (German: ‘Herleitungsordnung’).
Of course, obviously circular proofs will be avoided.

We use schematic propositional variables A, B, C, D (with or without indices)
to formulate the rules of the system.

With our Gentzen-style derivations, we will use expressions of the form '[formula]CP'
as abbreviations for proof assumptions (sometimes with indices); we have for instance

'[P∨Q]CP'     for 'P∨Q conditional proof assumption'
'[P→Q]PEC     for 'P→Q proof by exhaustive cases assumption'
'[Q∧P]IP'     for 'Q∧P indirect proof assumption'
'[R]PC1'       for 'R proof by cases assumption 1'
'[¬R∨S]'      for '¬R∨S' premise'

When applying theorems during a derivation, we write '[formula]Th'.

In Lean, there are two kinds of provable statements,
1) statements with named premises, such as
(h1 : P ∧ Q) (h2 : P → R) : R which we refer to as "argument forms";
2) statements without named premises, such as
(P ∧ Q ∧ (P → R)) → R which we refer to as "formulas"

----------------------------------------------------------------------
Basic Rules
----------------------------------------------------------------------

-- Abbreviation    Derivation           Rule Names

-- (MP)     A, A → B ⊢ B               (Modus Ponens)
-- (MT)     A → B, ¬B ⊢ ¬A             (Modus Tollens)
-- (DS1)    A ∨ B, ¬A ⊢ B              (Disjunctive Syllogism 1)
-- (DS2)    A ∨ B, ¬B ⊢ A              (Disjunctive Syllogism 2)
-- (∧E1)    A ∧ B ⊢ A                  (∧-Elimination 1 / Simplification 1)
1.2.5.1 Excursion: ∧-Component Extraction
-- (∧E2)    A ∧ B ⊢ B                  (∧-Elimination 2 / Simplification 2)
-- (∨I1)    A ⊢ A ∨ B                  (∨-Introduction 1 / Addition 1)
-- (∨I2)    B ⊢ A ∨ B                  (∨-Introduction 2 / Addition 2)
-- (∧I)     A, B ⊢ A ∧ B               (∧-Intro, Conjunction)
-- (ECQ)    A ∧ ¬A ⊢ B                 (Ex Contradictione Quodlibet)
-- (DNI)    A ⊢ ¬¬A                    (Double Negation Introduction)
-- (DNE)    ¬¬A ⊢ A                    (Double Negation Elimination)
-- (TA)     A → A                      (Trivial Argument)
-- (PC)    A ∨ B, A → C, B → C ⊢ C    (Disjunction, ∨-Elimination)

----------------------------------------------------------------------
Meta-Rules
----------------------------------------------------------------------

-- (IP)   Indirect Proof
-- (CP)   Conditional Proof
-- (PEC)  Proof by Exhaustive Cases



-----------------------------------------------------------------------
1.3 Basic Rules
----------------------------------------------------------------------



----------------------------------------------------------------------
-- 1.3.1 (MP) 		A, A → B ⊢ B 		(Modus Ponens)
----------------------------------------------------------------------

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"   |Lean form "at closing step"      |Gentzen-style derivation
have hA : A := ...                |have hA : A := ...               |k A 
have hAimpB : A → B := ...        |have hAimpB : A → B := ...       |l A → B 
have hB : B := hAimpB hA          |exact hAimpB hA                  |n B by MP from k,l


Examples

We begin with two examples in order to motivate a discussion about
clarity versus strict 1:1 correspondence between Lean proofs in tactic
mode and derivations in our natural deduction system.

Since the final step of a Lean proof often involves a closing command
such as `exact` (or alternatively `apply`), it is natural to address
this issue at the outset.

----------------------------------------------------------------------
Example 1: Perfect 1:1 Correspondence
----------------------------------------------------------------------
-/
example {P Q R : Prop} (h1 : P ∧ Q) (h2 : P → R) : R := by {
  have h1 : P ∧ Q := h1       -- 1 [P∧Q]Pr
  have h2 : P → R := h2       -- 2 [P→R]Pr
  have hP : P := h1.left      -- 3 P by ∧-Elimination1 from 1
  exact h2 hP                 -- 4 R by Modus Ponens from 2,3
}

/-
----------------------------------------------------------------------
Example 2: Explicit Construction of the Conclusion
----------------------------------------------------------------------

Here, the final step is decomposed into two Lean statements:
one constructing the result "have hR", and one closing the goal
"exact hR".
-/

example {P Q R : Prop} (h1 : P ∧ Q) (h2 : P → R) : R := by {
  have h1 : P ∧ Q := h1       -- 1 [P∧Q]Pr
  have h2 : P → R := h2       -- 2 [P→R]Pr
  have hP : P := h1.left      -- 3 P by ∧-Elimination1 from 1
  have hR : R := h2 hP        -- 4 R by Modus Ponens from 2,3
  exact hR               
}

/-
If one inspects the proof state after the final have statement in
Example 2, Lean reports that a term of type R has already been constructed,
while the goal ⊢ R remains open. The command exact hR then closes
this goal, provided that its type matches the goal.

Thus, Example 1 achieves a strict 1:1 correspondence between Lean
statements and derivation steps, whereas Example 2 separates
the construction of the conclusion from the termination of the proof.
Note that Lean’s closing step exact hR is administrative in nature
and has no direct logical counterpart on the side of the derivation.

This leads to a methodological choice:

1) Do we interpret Lean’s combination of term construction and goal closure
(as in Example 1) as adequately represented by a single derivation step
consisting of the conclusion together with its justification?

2) Or do we instead make Lean’s (optional) separation between term construction
and proof termination explicit, even though the latter has no direct
counterpart in the derivation?

4) A further possibility would be to introduce an artificial derivation step, e.g.

exact hR                  -- 5 R by Trivial Argument from 4

However, this move appears conceptually unmotivated and/or artificial. 

5) Or do we prefer a compromise as given by the following hybrid style:

----------------------------------------------------------------------
Example 3: Explicit Construction of the Conclusion (hybrid)
----------------------------------------------------------------------
-/
example {P Q R : Prop} (h1 : P ∧ Q) (h2 : P → R) : R := by {
  have h1 : P ∧ Q := h1       -- 1 [P∧Q]Pr
  have h2 : P → R := h2       -- 2 [P→R]Pr
  have hP : P := h1.left      -- 3 P by ∧-Elimination1 from 1
  have hR : R := h2 hP        -- 4 R by Modus Ponens from 2,3
  exact hR                    -- Lean: goal closed (non-numbered administrative step)             
}
/-
----------------------------------------------------------------------
Example 4: Perfect 1:1 Correspondence with the corresponding formula
----------------------------------------------------------------------

The situation changes slightly when proving formulas. In such cases, the
final step of the derivation coincides naturally with the closing of the main goal. 

-/

example {P Q R : Prop} : (P ∧ Q ∧ (P → R)) → R := by {
  intro h                            -- 1 [(P∧Q)∧(P→R)]CP
  have hP : P := h.left              -- 2 P by ∧-Elimination1 from 1
  have hPQR : Q ∧ (P → R) := h.right -- 3 Q∧(P→R) by ∧-Elimination2 from 1
  have hPR : P→R := hPQR.right       -- 4 P→R by ∧-Elimination2 from 3
  have hR : R := hPR hP              -- 5 R by Modus Ponens from 2,4
  exact hR                           -- 6 (P ∧ Q ∧ (P → R)) → R by CP from 1-4
}

/-
Summary of Observations

1) The rule Modus Ponens (MP) admits a straightforward 1:1 realization
   in Lean for both argument forms and formulas.

2) Subtleties arise only at the level of proof (and subproof) termination.
   In proofs with argument forms, Lean typically requires an explicit closing
   command (`exact`, `apply`), which does not correspond to a
   separate derivation step in Gentzen-style systems.

3) In contrast, in conditional proofs (CP), the discharge of the
   assumption coincides with Lean's mechanism of closing the goal.
   Hence, in such cases, the 1:1 correspondence is preserved without
   any adjustment. (As we shall see, this holds only for single
   applications of (CP) and other meta-rules involving assumption discharge,
   as will become relevant in more complex derivations.

This leads to a fundamental methodological choice:
one may either
(a) relax strict 1:1 correspondence,
(b) refine the notion of an atomic Lean proof step, or
(c) adopt a hybrid derivation style. 
-/


----------------------------------------------------------------------
-- 1.3.2 (MT) 		A → B, ¬B ⊢ ¬A 		(Modus Tollens)
----------------------------------------------------------------------
/-
Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"   |Lean form "at closing step"    |Gentzen-style derivation
have hAimpB : A → B := ...        |have hAimpB : A → B := ...     |k A → B  
have hnB : ¬B := ...              |have hnB : ¬B := ...           |l ¬B  
have hnA : ¬A := mt hAimpB hnB    |exact mt hAimpB hnB            |n ¬A by MT from k,l 


Examples

----------------------------------------------------------------------
Example 1: Perfect 1:1 Correspondence
----------------------------------------------------------------------
-/
example (P Q : Prop) (h1 : ¬P) (h2 : ¬P → (Q → P)) : ¬Q := by {
  have h1 : ¬P := h1            -- 1 [¬P]Pr
  have h2 : ¬P → (Q → P) := h2  -- 2 [¬P→(Q→P)]Pr
  have hQP : (Q → P) := h2 h1   -- 3 (Q→P) by Modus Ponens from 1,2
  exact mt hQP h1               -- 4 ¬Q by Modus Tollens from 1,3
}
/-
Here we have expressed the Modus Tollens operation by making use of
the Lean lemma mt from Mathlib. Hovering over "mt" inside the "exact"
expression the mouse-over info shows:

mt := {a b : Prop}
      (h₁ : a → b) (h₂ : ¬b) : ¬a 

This corresponds exactly to the rule (MT) as implemented in Lean’s Mathlib.
In the above derivation the MT operation and the final "exact"
are not separated. Again, if we separate these two operations we arrive at the

----------------------------------------------------------------------
Example 2: Explicit Construction of the Conclusion
----------------------------------------------------------------------
-/
example (P Q : Prop) (h1 : ¬P) (h2 : ¬P → (Q → P)) : ¬Q := by {
  have h1 : ¬P := h1            -- 1 [¬P]Pr
  have h2 : ¬P → (Q → P) := h2  -- 2 [¬P→(Q→P)]Pr
  have hQP : (Q → P) := h2 h1   -- 3 (Q→P) by Modus Ponens from 1,2
  have hnQ : ¬Q := mt hQP h1    -- 4 ¬Q by Modus Tollens from 1,3
  exact hnQ
}
/-
Again, the 1:1 correspondence gets lost but might be preserved by
an additional Lean information statement:

----------------------------------------------------------------------
Example 3: Explicit Construction of the Conclusion (hybrid)
----------------------------------------------------------------------
-/
example (P Q : Prop) (h1 : ¬P) (h2 : ¬P → (Q → P)) : ¬Q := by {
  have h1 : ¬P := h1            -- 1 [¬P]Pr
  have h2 : ¬P → (Q → P) := h2  -- 2 [¬P→(Q→P)]Pr
  have hQP : (Q → P) := h2 h1   -- 3 (Q→P) by Modus Ponens from 1,2
  have hnQ : ¬Q := mt hQP h1    -- 4 ¬Q by Modus Tollens from 1,3
  exact hnQ                     -- Lean: goal closed
}
/-

As with Modus Ponens (MP) before, the application of (MT) preserves
the 1:1 correspondence when the separated "exact" coincides with the
discharge of the assumption in a conditional proof (CP), if dealing
with formulas. 
----------------------------------------------------------------------
Example 4: Perfect 1:1 Correspondence with the corresponding formula
----------------------------------------------------------------------
-/
example (P Q : Prop) : ((¬P ∧ (¬P → (Q → P))) → ¬Q) := by {
  intro h                       -- 1 [¬P∧(¬P→(Q→P))]CP
  have h1 : ¬P → (Q → P) := h.right -- 2 ¬P → (Q → P) by ∧-Elimination from 1
  have hnP : ¬P := h.left       -- 3 ¬P by ∧-Elimination from 1
  have hQP : (Q → P) := h1 hnP  -- 4 (Q→P) by Modus Ponens from 2,3
  have hnQ : ¬Q := mt hQP hnP   -- 5 ¬Q by Modus Tollens from 3,4
  exact hnQ                     -- 6 ((¬P ∧ (¬P → (Q → P))) → ¬Q) by CP from 1-5
}
/-

Summary: As illustrated by the rules (MP) and (MT), the most promising cases for
preserving a 1:1 correspondence are given by the first and the last examples:

1) for argument forms we accept expressions of the form ‘exact + operation’ to
   construct the operation and close the goal in one command only.

    "exact h2 hP                 -- 4 R by Modus Ponens from 2,3"
    "exact mt hQP h1             -- 4 ¬Q by Modus Tollens from 1,3"

  This choice may seem critical for purists who want to preserve granularity of
  primitive steps at any cost, but this concerns only the Lean representation;
  the derivation itself remains unchanged.

2) for proofs of formulas we will accept the closing "exact hP" (where 'P'
   denotes the current goal formula) as natural counterpart for the discharging
   of the final assumption in a derivation.

For the time being, we adopt these solutions as canonical. This does not exclude
the alternative approaches discussed above, namely abandoning strict 1:1
correspondence or adopting a hybrid style. We keep these options open until we
encounter rules that force a more definitive choice. This choice is guided by our
extensional perspective introduced in our methodological outline (Section 1.1).

Accordingly, in the following we will illustrate further rules primarily using
examples of type (1) and (2). 
-/



----------------------------------------------------------------------
-- 1.3.3 (DS1) 		A∨B, ¬A ⊢ B 		(Disjunctive Syllogism 1)
----------------------------------------------------------------------
/-
Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"           |Lean form "at closing step"       |Gentzen form
have hAorB : A ∨ B := ...                 |have hAorB : A ∨ B := ...         |k A ∨ B  
have hnA : ¬A := ...                      |have hnA : ¬A := ...              |l ¬A   
have hB : B := Or.resolve_left hAorB hnA  |exact Or.resolve_left hAorB hnA   |n B by DS1 from k,l 


Examples
-/

example {P Q R T S : Prop} (h1 : P) (h2 : P → (Q → ¬R)) (h3 : ¬¬R) (h4 : Q ∨ (T∧S)) : T := by {
  have h1 : P := h1              -- 1 [P]Pr
  have h2 : P → (Q → ¬R) := h2   -- 2 [P→(Q→¬R)]Pr
  have h3 : ¬¬R := h3            -- 3 [¬¬R]Pr
  have h4 : Q ∨ (T∧S) := h4      -- 4 [Q∨(T∧S)]Pr
  have hQnR : (Q → ¬R) := h2 h1  -- 5 (Q→¬R) by MP from 1,2
  have hnR : ¬Q := mt hQnR h3    -- 6 ¬Q by MT from 3,5
  have hTS : (T∧S) := Or.resolve_left h4 hnR -- 7 T∧S by DS1 from 4,6 
  exact hTS.left                 -- 8 T by ∧-Elimination1 from 7
}                    

/- 
The corresponding Lean lemma for (DS1) is Or.resolve_left, part of Mathlib.
Inspecting its type yields its name: 
  
  Or.resolve_left {a b : Prop} (h : a ∨ b) (na : ¬a) : b.

From an extensional perspective, such library lemmas can be treated as direct
implementations of inference rules.
  
-/
example {P Q R S T : Prop} : (P ∧ (P → (Q → ¬R)) ∧ ¬¬R ∧ (Q ∨ (T ∧ S))) → T := by {
  intro h                                   -- 1 [P∧(P→(Q→¬R))∧¬¬R∧(Q∨(T∧S))]CP
  have h1 : P := h.left                     -- 2 P by ∧-Elimination1 from 1 
  have h2 : (P → Q → ¬R) ∧ ¬¬R ∧ (Q ∨ (T ∧ S)) := h.right 
                                            -- 3 (P→Q→¬R)∧¬¬R∧(Q∨(T∧S)) by ∧-Elimination2 from 1
  have h3 : (P → Q → ¬R) := h2.left         -- 4 P→Q→¬R by ∧-Elimination1 from 3
  have h4 : ¬¬R ∧ (Q ∨ (T ∧ S)) := h2.right   -- 5 ¬¬R∧(Q∨(T∧S)) by ∧-Elimination2 from 3
  have h5 : Q ∨ (T ∧ S) := h4.right         -- 6 Q∨(T∧S) by ∧-Elimination2 from 5 
  have hQnR : (Q → ¬R) := h3 h1             -- 7 Q→¬R by Modus Ponens from 1,4
  have hnnR : ¬¬R := h4.left                -- 8 ¬¬R by ∧-Elimination1 from 5
  have hnR : ¬Q := mt hQnR hnnR             -- 9 ¬Q by Modus Tollens from 7,8
  have hTS : (T ∧ S) := Or.resolve_left h5 hnR--10 (T∧S) by DS1 from 6,9
  have hT : T := hTS.left                   --11 T by ∧-Elimination1 from 10
  exact hT                                  --12 (P∧(P→(Q→¬R))∧¬¬R∧(Q∨(T∧S)))→T by CP from 1
}
/-



----------------------------------------------------------------------
-- 1.3.4 (DS2) 		A∨B, ¬B ⊢ A 		(Disjunctive Syllogism 2)
----------------------------------------------------------------------

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"           |Lean form "at closing step"      |Gentzen-style derivation
have hAorB : A ∨ B := ...                 |have hAorB : A ∨ B := ...        |k A ∨ B  
have hnB : ¬B := ...                      |have hnB : ¬B := ...             |l ¬B  
have hA : A := Or.resolve_right hAorB hnB |exact Or.resolve_right hAorB hnB |n A by DS2 from k,l

-/ 

example {P Q R : Prop} (h1 : (P → Q) ∨ R) (h2 : P ∧ ¬R) : Q := by {
  have h1 : (P → Q) ∨ R := h1         -- 1 [(P→Q)∨R]Pr
  have h2 : P ∧ ¬R := h2              -- 2 [P∧¬R]Pr
  have hnR : ¬R := h2.right           -- 3 ¬R by ∧-Elimination2 from 2
  have hPQ : (P → Q) := Or.resolve_right h1 hnR -- 4 P → Q by DS2 from 1,3
  have hP : P := h2.left              -- 5 P by ∧-Elimination1 from 2
  exact hPQ hP                        -- 6 Q by Modus Ponens from 4,5

}

example {P Q R : Prop} : ((P → Q) ∨ R) ∧ (P ∧ ¬R) → Q := by {
  intro h                             -- 1 [((P→Q)∨R)∧(P∧¬R)]CP
  have h1 : (P → Q) ∨ R := h.left     -- 2 (P→Q)∨R by ∧-Elimination1 from 1
  have h2 : (P ∧ ¬R) := h.right       -- 3 P∧¬R by ∧-Elimination2 from 1
  have hP : P := h2.left              -- 4 P by ∧-Elimination1 from 3
  have hnR : ¬R := h2.right           -- 5 ¬R by ∧-Elimination2 from 3
  have hPQ : (P → Q) := Or.resolve_right h1 hnR -- 6 P → Q by DS2 from 2,5
  have hQ : Q := hPQ hP               -- 7 Q by Modus Ponens from 4,6
  exact hQ                            -- 8 ((P → Q) ∨ R) ∧ (P ∧ ¬R) → Q by CP from 1-7
}
/- Lean's corresponding Lemma for (DS2) is Or.resolve_right, part of the Mathlib:
  
           Or.resolve_right {a b : Prop} (h : a ∨ b) (nb : ¬b) : a.
  
  This can be seen as mouse-over info when hovering over its name.



----------------------------------------------------------------------
-- 1.3.5 (∧E1) 		A ∧ B ⊢ A 		(∧-Elimination 1, Simplification 1)
----------------------------------------------------------------------


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"   |Lean form "at closing step"    |Gentzen-style derivation
have hAandB : A ∧ B := ...        |have hAandB : A ∧ B := ...     |k A ∧ B
have hA : A : hAandB.left         |exact hAandB.left              |n A by ∧-Elimination1 from k


In the previous section we have extensively used ∧-Elimination 1 and ∧-Elimination 2
and and have thereby shown that these operations pose no difficulty in preserving a 1:1
correspondence between Lean Tactic proofs and Natural deduction.
The corresponding Lean Lemmas in Mathlib are

And.left {a b : Prop} (self : a ∧ b) : a

and

And.right {a b : Prop} (self : a ∧ b) : b


----------------------------------------------------------------------
-- 1.2.5.1 Excursion: ∧-Component Extraction
----------------------------------------------------------------------

In our second example for (DS1) we experienced how laborious and cumbersome it can be to extract
single components (conjuncts) from the [P∧(P→(Q→¬R))∧¬¬R∧(Q∨(T∧S))]CP assumption. So what to do if
a more complex formula comes along, like: (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) → (S ∧ T) ?

Note that '∧' is right-associative. The hypothesis (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) is parsed
by Lean as

                 P ∧ (Q ∧ (R ∧ (S ∧ (T ∧ (P1 ∧ (P2 ∧ P3))))))

So one might think that the following Gentzen-Lean proof would be acceptable from a viewpoint of
effectiveness (and usual practice of logicians and mathematicians) by concatenating the .right
and .left operations several times:
-/

example {P Q R S T P1 P2 P3 : Prop} :
  (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) → (S ∧ T) := by {
  intro h                                 -- 1 [(P∧Q∧R∧S∧T∧P1∧P2∧P3)]CP
  have hS : S := h.right.right.right.left -- 2 S by 3-times ∧-Elimination2
                                          --   and one ∧-Elimination1 from 1
  have hT : T := h.right.right.right.right.left -- 3 T by 4-times ∧-Elimination2
                                                --   3-times ∧-Elimination1 from 1
  have hST : S ∧ T := And.intro hS hT     -- 4 S∧T by ∧-Intro from 2,3
  exact hST                               -- 5 (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) → (S ∧ T)
                                          -- by CP from 1-4
}
/-
But, though 1:1, here we obtain only a pseudo-derivation, since expressions such as

"by 3-times ∧-Elimination2 and one ∧-Elimination1 from 1"

are not part of the formal meta-language of derivations.

On the other hand, a correct derivaton turns out to be quite lengthy!
Again, compare the proofs with the structure of the premises:

                 P ∧ (Q ∧ (R ∧ (S ∧ (T ∧ (P1 ∧ (P2 ∧ P3))))))
-/

example {P Q R S T P1 P2 P3 : Prop} :
  (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) → (S ∧ T) := by {
  intro h             -- 1 [(P∧Q∧R∧S∧T∧P1∧P2∧P3)]CP
  have h1 := h.right  -- 2 Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3 by ∧-Elimination2 from 1
  have h2 := h1.right -- 3 R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3 by ∧-Elimination2 from 2
  have h3 := h2.right -- 4 S ∧ T ∧ P1 ∧ P2 ∧ P3 by ∧-Elimination2 from 3
  have hS := h3.left  -- 5 S by ∧-Elimination1 from 4 
  have h4 := h3.right -- 6  T ∧ P1 ∧ P2 ∧ P3
  have hT := h4.left  -- 7 T by ∧-Elimination1 from 6
  have hST : S ∧ T := And.intro hS hT -- 8 S∧T by ∧-Intro from 5,7
  exact hST           -- 9 (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) → (S ∧ T) by CP from 1-8
}
/-
Sticking to the 1:1 desideratum does not mean to be necessarily cumbersome. We would like
to meet a general projection rule like

(∧CE) ∧-Component Extraction

For n ≥ 2 and 1 ≤ i ≤ n:

  A₁ ∧ A₂ ∧ ... ∧ Aₙ
  ------------------   (∧-Projectionₙ, i)
          Aᵢ

Strictly speaking, this is a rule schema rather than a single inference rule.
This schema allows direct access to any component of a right-associated
conjunction without explicitly performing multiple elimination steps.

It is a derived rule, obtained by iterated applications of ∧-elimination.
In Lean (∧CE) corresponds to several solutions. Our choice here is 

pattern matching (or destructuring pattern) 
e.g.: have ⟨..., hS, ...⟩ := h

-/
--pattern matching
example {P Q R S T P1 P2 P3 : Prop} :
  (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) → (S ∧ T) := by {
    intro h                             --1 [(P∧Q∧R∧S∧T∧P1∧P2∧P3)]CP
    have ⟨_, _, _, hS, _, _, _, _⟩ := h -- 2 S by ∧CE from 1
    have ⟨_, _, _, _, hT, _, _, _⟩ := h -- 3 T by ∧CE from 1
    have hST : S ∧ T := And.intro hS hT -- 4 S ∧ T by ∧-Intro
    exact hST                     -- 5 (P ∧ Q ∧ R ∧ S ∧ T ∧ P1 ∧ P2 ∧ P3) → (S ∧ T)
                                  --   by CP from 1-4               
}
/-
The notation ⟨a, b⟩ denotes the canonical constructor of a conjunction.
It corresponds to the introduction rule for ∧ and is syntactic sugar for

  And.intro a b.

Conceptually, it can be understood as a pairing operation.

Conjunctions in Lean thus admit two complementary operations:

  • construction via pairing (⟨a, b⟩),
  • decomposition via pattern matching (⟨..., x, ...⟩ := h).

These correspond to the introduction and elimination behavior of ∧,
but are expressed in a structurally more direct way.

Summary: The above example illustrates that maintaining a strict 1:1 correspondence
at the level of primitive rules may lead to impractical derivations. Derived
rule schemata such as (∧CE) provide a principled way to recover both efficiency
and readability.”
-/



----------------------------------------------------------------------
-- 1.3.6 (∧E2) 		A ∧ B ⊢ B 		(∧-Elimination 2, Simplification 2)
----------------------------------------------------------------------
/-

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"  |Lean form "at closing step"  |Gentzen-style derivation 
have hAandB : A ∧ B := ...       |have hAandB : A ∧ B := ...   |k A ∧ B
have hB : B := hAandB.right      |exact hAandB.right           |n B by ∧-Elimination2 from k


Since we have extensively discussed (∧E1) and the rule schema (∧CE), we will keep it short with its dual (∧E2) and try an indirect proof, including applications of three theorems (denoted ‘Th’) not yet introduced:
  
-/

example {P Q : Prop} : (P → Q) ∨ ¬Q := by {
  by_contra hnPQ                              -- 1 [¬((P→Q)∨¬Q)]IP
  have h1 : ¬(P → Q) ∧ ¬¬Q := not_or.mp hnPQ  -- 2 ¬(P→Q)∧¬¬Q by Th ¬(A∨B)→(¬A∧¬B) from 1
  have h2 : ¬(P → Q) := h1.left               -- 3 ¬(P→Q) by ∧E1 from 2
  have hnnQ : ¬¬Q := h1.right                 -- 4 ¬¬Q by ∧E2 from 2
  have hPnQ : (P ∧ ¬Q) := Classical.not_imp.mp h2 -- 5 P∧¬Q by Th ¬(A→B)→(A∧¬B) from 3
  have hQ : Q := of_not_not hnnQ              -- 6 Q by Th ¬¬A→A from 4
  have hnQ : ¬Q := hPnQ.right                 -- 7 ¬Q by ∧E2 from 5
  have h_goal : Q ∧ ¬Q := And.intro hQ hnQ    -- 8 Q∧¬Q by ∧-Intro from 6,7
  contradiction                               -- 9 (P → Q) ∨ ¬Q by IP from 1-8
}
/-
If you hover over the Lean statement "contradiction", the mouse-over info explains
what its effect is: "contradiction closes the main goal if its hypotheses are "trivially contradictory". This corresponds to the discharging of the IP assumption. Thus,
a single application of the rule of Indirect Proof preserves the 1:1 correspondence, in
line with our earlier observations on meta-rules involving assumption discharge.

We will keep on using the basic rules (∧E1) and (∧E2) and only use the derived rule schema (∧CE)
in cases where more than two conjuncts are involved in the premise.
-/



----------------------------------------------------------------------
-- 1.3.7 (∨I1) 		A ⊢ A ∨ B 		(∨-Intro1, Addition 1)
----------------------------------------------------------------------
/-

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"   |Lean form "at closing step"  |Gentzen-style derivation 
have hA : A := ...                |have hA : A := ...           |k A
have hAorB : A ∨ B := Or.inl hA   |exact Or.inl hA              |n A ∨ B by ∨-Intro1 from k


We make use of the Lean Lemma: Or.inl {a b : Prop} (h : a) : a ∨ b
also called "left injection into an Or"
-/

example {P Q : Prop} (h : P ∧ Q) :(P ∨ Q) := by {
  have h : P ∧ Q := h    -- 1 [P∧Q]Pr
  have hP : P := h.left  -- 2 P by ∧-Elimination1 from 1
  exact Or.inl hP        -- 3 P∨Q by ∨-Intro1 from 2
 }

example {P Q : Prop} : (P ∧ Q) → (P ∨ Q) := by {
  intro h               -- 1 [P∧Q]CP
  have hP : P := h.1    -- 2 P by ∧-Elimination1 from 1
  have hPorQ : P ∨ Q := Or.inl hP -- 3 P ∨ Q by ∨-Intro1 from 2
  exact hPorQ           -- 4 (P ∧ Q) → (P ∨ Q) by CP from 1-3
}



----------------------------------------------------------------------
-- 1.3.8 (∨I2) 		B ⊢ A ∨ B 		(∨-Intro2, Addition 2)
----------------------------------------------------------------------
/-

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"   |Lean form "at closing step"  |Gentzen-style derivation
have hB : B := ...                |have hB : B := ...           |k B
have hAorB : A ∨ B := Or.inr hB   |exact Or.inr hB              |n A ∨ B by ∨-Intro2 from k


We make use of the Lean Lemma: Or.inr {a b : Prop} (h : b) : a ∨ b
also called "right injection into an Or"
-/

example {P Q R : Prop} (h : P ∧ Q) : (R ∨ P) ∧ Q := by {
  have h : P ∧ Q := h             -- 1 [P∧Q]Pr
  have hP : P := h.left           -- 2 P by ∧-Elimination1 from 1
  have h_new : R ∨ P := Or.inr hP -- 3 R ∨ P by ∨-Intro2 from 2
  have hQ : Q := h.right          -- 4 Q by ∧-Elimination2 from 1
  exact And.intro h_new hQ        -- 5 (R ∨ P) ∧ Q by ∧-Intro from 3,4

}

example {P Q R : Prop} : (P ∧ Q) → (R ∨ P) ∧ Q := by {
  intro h                         -- 1 [P∧Q]CP
  have hP : P := h.left           -- 2 P by ∧-Elimination1 from 1
  have h_new : R ∨ P := Or.inr hP -- 3 R ∨ P by ∨-Intro2 from 2
  have hQ : Q := h.right          -- 4 Q by ∧-Elimination2 from 1
  have final : (R ∨ P) ∧ Q := And.intro h_new hQ -- 5 (R ∨ P) ∧ Q by ∧-Intro from 3,4
  exact final                     -- 6 (P ∧ Q) → (R ∨ P) ∧ Q  by CP from 1-5
}

/-
Together, Or.inl and Or.inr provide fully symmetric implementations of the two
introduction rules for disjunction.

At this point, all basic local inference rules considered so far admit a straightforward
linear 1:1 representation in Lean.
-/



----------------------------------------------------------------------
-- 1.3.9 (∧I) 		A,B ⊢ A ∧ B 		(∧-Intro, Conjunction)
----------------------------------------------------------------------
/-

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"         |Lean form "at closing step"   |Gentzen-style derivation 
have hA : A := ...                       |have hA : A := ...           |k A 
have hB : B := ...                       |have hB : B := ...           |l B
have hAandB : A ∧ B := And.intro hA hB   |exact And.intro hA hB        |n A ∧ B by ∧-Intro from k,l

The corresponding Lean lemma for conjunction introduction is And.intro:

          And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

Alternatively we can use the anonymous constructors ⟨⟩ for constructing the conjunction
as was mentioned at the end of Section 1.3.5.1; instead of "exact And.intro ..." you 
can write

                    exact ⟨hA, hB⟩

--Examples
-/

example {P Q R : Prop} (h1 : P ∧ Q) (h2 : Q ∧ R) : P ∧ R := by {
  have h1 : P ∧ Q := h1         -- 1 [P∧Q]Pr
  have h2 : Q ∧ R := h2         -- 2 [Q∧R]Pr
  have hP : P := h1.left        -- 3 P by ∧-Elimination1 from 1 
  have hR : R := h2.right       -- 4 R by ∧-Elimination2 from 2
  exact And.intro hP hR         -- 5 P ∧ R by ∧-Intro from 3,4
  --alternatively:  exact ⟨hP, hR⟩
}

example {P Q R : Prop} : ((P ∧ Q) ∧ (Q ∧ R)) → (P ∧ R) := by {
  intro h                       -- 1 [(P∧Q)∧(Q∧R)]CP
  have hPQ : P ∧ Q := h.left    -- 2 P∧Q by ∧-Elimination1 from 1
  have hQR : Q ∧ R := h.right   -- 3 Q∧R by ∧-Elimination2 from 1 
  have hP : P := hPQ.left       -- 4 P by ∧-Elimination1 from 2
  have hR : R := hQR.right      -- 5 R by ∧-Elimination2 from 3
  have final : P ∧ R := And.intro hP hR -- 6 P∧R by ∧-Intro from 4,5
--alternatively:   have final : P ∧ R := ⟨hP, hR⟩
  exact final                   -- 7 ((P ∧ Q) ∧ (Q ∧ R)) → (P ∧ R) by CP from 1-6 
}
/-
Together with destructuring patterns for elimination, anonymous constructors
provide a compact structural notation for conjunctions in Lean. Nevertheless,
we will adopt And.intro as the canonical form of conjunction introduction.
Anonymous constructors will only be used for conjunctions with more than two
conjuncts.
-/



----------------------------------------------------------------------------------------
-- 1.3.10 (ECQ) 	A∧¬A ⊢ B 		(Ex Contradictione Quodlibet, Ex Falso Quodlibet, ex falso)
----------------------------------------------------------------------------------------
/-

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "Terminal contradiction closure"         |Gentzen-style derivation 
have hcont : A ∧ ¬A := ...                         |k A∧¬A 
contradiction                                      |n B by ECQ from k 
                             

Lean form "Explicit contradiction-based construction"   |Gentzen-style derivation 
have cont : A ∧ ¬A := ...                               |k A∧¬A by ...
have hgoal : B := absurd hA hnA                         |n B by ECQ from k
exact hgoal                                             |m ... → B by CP from 1-n

Naturally, applications of (ECQ) typically occur at the end of a (sub-)proof. In such a 
case we will have to introduce two slightly different solutions depending on what type
of proposition is to be proved.

For argument forms, we can use tactic "contradiction" which searches inside the context for contradicting propositions and if found, closes the proof immediately. This tactic does not require the explicit construction of a contradiction like "C∧¬C" but rather operates along the equivalent rule
A, ¬A ⊢ B. Nevertheless, since we prefer explicitness, we do not wish to avoid the moment many mathematicians enjoy most: explicitly exhibiting the contradiction A ∧ ¬A. QED.

For formulas we prefer the application of the "absurd" tactic which also detects contradictory propositions in the context (therefore acting in line with rule A, ¬A ⊢ B) but does not close
the goal! This has to be done in a separate step "exact" which allows us to close the conditional
proof in parallel to the derivation. So after constructing the explicit contradiction
using "have", we use another "have" to explicitly construct the goal and finally we close the
goal by "exact".

Thus, contradiction behaves as a terminal proof operation, whereas absurd permits the explicit construction of the target proposition before the final closing step.

-/

--argument form
example {P Q R : Prop} (h1 : P ∧ ¬Q) (h2 : ¬P) : R := by {
  have h1 : (P ∧ ¬Q) := h1    -- 1 [P∧¬Q]Pr
  have hnP : ¬P := h2         -- 2 [¬P]Pr
  have hP : P := h1.left      -- 3 P by ∧-Elimination1 from 1
  have hcont : P ∧ ¬P := And.intro hP hnP -- 4 P∧¬P by ∧-Intro from 2,3
  contradiction               -- 5 R by ECQ from 4
}

/-
From an extensional point of view, the solution works like this: first, we explicitly
formulate a contradiction

      have hcont : P ∧ ¬P := And.intro hP hnP

This corresponds to "P ∧ ¬P by ∧-Intro" in the derivation. In the final step, we use
contradiction: this automatically searches for conflicting statements within the previous
course of the proof. Whether Lean restricts itself to P and ¬P or uses the also present
statement P ∧ ¬P is irrelevant to us; in any case, the proof is completed with the goal R.
-/

--formula
example {P Q R : Prop} : ((P ∧ ¬Q) ∧ ¬P) → R := by {
  intro h                       -- 1 [P∧¬Q)∧¬P]CP
  have h1 : (P ∧ ¬Q) := h.left  -- 2 P∧¬Q by ∧-Elimination1 from 1 
  have hnP : ¬P := h.right      -- 3 ¬P by ∧-Elimination2 from 1
  have hP : P := h1.left        -- 4 P by ∧-Elimination1 from 2
  have hcont : P ∧ ¬P := And.intro hP hnP -- 5 P∧¬P by ∧-Intro from 3,4
  have hR : R := absurd hP hnP  -- 6 R by ECQ from 5
  exact hR                      -- 7 ((P ∧ ¬Q) ∧ ¬P) → R by CP from 1-6
}

/-
In this solution, we also first construct the contradiction, but then we explicitly
formulate the solution R (as the conclusion of the contradiction). Finally, we
complete the conditional proof.
-/



----------------------------------------------------------------------
-- 1.3.11 (DNI) 	A ⊢ ¬¬A 		(Double Negation Intro, DN-Intro)
----------------------------------------------------------------------
/-


The Lean lemma used here for (DNI) is not_not_intro:

        not_not_intro {p : Prop} (h : p) : ¬¬p

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"     |Lean form "at closing step"   |Gentzen-style derivation 
have hA : A := ...                  |have hA : A := ...            |k A 
have hnnA : ¬¬A := not_not_intro hA |exact not_not_intro hA        |n ¬¬A by DNI from k

--Examples
-/
example {P Q : Prop} (h1: ¬Q → ¬P) (h2 : P) : ¬¬Q := by {
  have h1 : ¬Q → ¬P := h1           -- 1 [¬Q→¬P]Pr
  have h2 : P := h2                 -- 2 [P]Pr
  have h3 : ¬¬P := not_not_intro h2 -- 3 ¬¬P by DNI from 2
  exact mt h1 h3                    -- 4 ¬¬Q by MT from 1,3
}

example {P Q : Prop} : ((¬Q → ¬P) ∧ P) → ¬¬Q := by {
  intro h                           -- 1 [(¬Q→¬P)∧P]CP
  have h1 : (¬Q → ¬P) := h.left     -- 2 ¬Q → ¬P by ∧-Elimination1 from 1
  have h2 : P := h.right            -- 3 P by ∧-Elimination2 from 1
  have h3 : ¬¬P := not_not_intro h2 -- 4 ¬¬P by DNI from 3
  have final : ¬¬Q := mt h1 h3      -- 5 ¬¬Q by MT from 2,4
  exact final                       -- 6 ((¬Q → ¬P) ∧ P) → ¬¬Q by CP from 1
}


---------------------------------------------------------------------------
-- 1.3.12 (DNE) 	¬¬A ⊢ A 		(Double Negation Elimination, DN-Elimination)
---------------------------------------------------------------------------
/-


DNE is a rule of classical propositional logic, in Lean it requires `open Classical`
placed at the top of a .lean file.

The Lean lemma used for (DNE) is `of_not_not`:

         of_not_not {a : Prop} : ¬¬a → a

Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"   |Lean form "at closing step"   |Gentzen-style derivation 
have hnnA : ¬¬A := ...            |have hnnA : ¬¬A := ...        |k ¬¬A
have hA : A := of_not_not hnnA    |exact of_not_not hnnA         |n A by DNE from k
-/

example {P Q : Prop} (h1 : (P → Q)) (h2 : ¬¬P) : Q := by {
  have hPQ : P → Q := h1          -- 1 [P→Q]Pr
  have hnnP : ¬¬P := h2           -- 2 [¬¬P]Pr
  have hP : P := of_not_not hnnP  -- 3 P by DN-Elimination from 2
  exact hPQ hP                    -- 4 Q by MP from 1,3
}

example {P Q : Prop} : ((P → Q) ∧ ¬¬P) → Q := by {
  intro h                         -- 1 [(P→Q)∧¬¬P]CP
  have hnnP : ¬¬P := h.right      -- 2 ¬¬P by ∧-Elimination2 from 1
  have hPQ : P → Q := h.left      -- 3 (P → Q) by ∧-Elimination1 from 1
  have hP : P := of_not_not hnnP  -- 4 P by DN-Elimination from 2
  have hQ : Q := hPQ hP           -- 5 Q by MP from 3,4
  exact hQ                        -- 6 ((P → Q) ∧ ¬¬P) → Q by CP from 1-5
}




-----------------------------------------------------------------------------
-- 1.3.13 (TA) 		A ⊢ A 			(Trivial Argument, Repetition, Logical Identity)
----------------------------------------------------------------------


/-
Interestingly enough, there is no Lean lemma in Mathlib that represents
the Trivial Argument in propositional logic. We first show a somewhat
tricky option for obtaining a 1:1 correspondence, but we will dismiss it later.


-/
-- argument form
example {P Q : Prop} (h1 : P ∨ Q) (h2 : P → Q) : Q := by {
  have hPorQ : P ∨ Q := h1   -- 1 [P∨Q]Pr
  have hPimpQ : P → Q := h2  -- 2 [P→Q]Pr 
  rcases hPorQ with hP | hQ  -- 3 [P]PC1
  exact hPimpQ hP            -- 4 Q by MP from 2,3
  have hQ : Q := hQ          -- 5 [Q]PC2
  have hQ' : Q := hQ         -- 6 Q by TA from 5
  exact hQ'                  -- 7 Q by PC from 3-6
}

/-
Note that in line 5 we assume the second case Q by repeating the assumption provided
by the "rcases hPorQ with hP | hQ" tactic - a typical redundant step but good
for the human reader. Then we transfer the value "Q" (more precisely "the proof of "Q")
from one variable to another to simulate (TA) in line 6. Finally we close the goal Q
by an exact + new variable. If you find this move quirky, we would agree.

A seemingly better way to achieve a good Lean representation of (TA) consists in proving
(TA) and using its proof as lemma in other proofs. Though (TA) is part of our basic rules
and one should not need to prove it, the proof only serves the formalization of the logical
system (TA) is part of.
-/

theorem trivial_arg {A : Prop} (h : A) : A := by {
  have hA : A := h        -- 1 [A]Pr         
  by_contra hnA           -- 2 [¬A]IP
  have h_cont : A ∧ ¬A := And.intro hA hnA -- 3 A ∧ ¬A by ∧-Intro from 1,2 
  contradiction           -- 4 A by IP from 2-3
}

/-
No doubt that some people would prefer the 1-liner (we don't):
-/
example {A : Prop} (h : A) : A := by {
  exact h
}

--argument form
example {P : Prop} (h : P ∨ P) : P := by {
  have h : P ∨ P := h             -- 1 [P∨P]Pr
  rcases h with hP | hP           -- 2 [P]PC1
  exact trivial_arg hP            -- 3 P by TA from 2
  have h1 : P := hP               -- 4 [P]PC2
  have h2 : P := trivial_arg hP   -- 5 P by TA from 4
  exact h2                        -- 6 P by PC from 2-5
}

--formula
example {P : Prop} : (P ∨ P) → P := by {
  by_contra hnP                           -- 1 [¬((P∨P)→P)]IP
  have h1 : (P ∨ P) ∧ ¬P := Classical.not_imp.mp hnP  -- 2 (P∨P)∧¬P by Th ¬(a→b)→(a ∧ ¬b) from 1
  have h2 : (P ∨ P) := h1.left            -- 3 P ∨ P by ∧-Elimination1 from 2 
  have h3 : ¬P := h1.right                -- 4 ¬P by ∧-Elimination2 from 2
  have h4 : P := Or.resolve_right h2 h3   -- 5 P by DS2 from 3,4
  have h5 : P := trivial_arg h4           -- 6 P by TA from 5
  have cont : P ∧ ¬ P := And.intro h4 h3  -- 7 P∧¬P by ∧-Intro from 4,6
  contradiction                           -- 8 P by IP from 1-7 
}
/-
In the above proof line 6 is redundant.

In fact, both ways of representing (TA) are extensionally the same. This can be observed in the Lean Info View where variable P has at least two names "h4 h5 : P" or "hQ hQ' : Q".
Nevertheless, our suggestion for a canonical representation of TA in Lean is "trivial_arg",
our local lemma - only because it appears less quirky. 


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form "at non-closing step"   |Lean form "at closing step"    |Gentzen-style derivation
have hA : A := ...                |have hA : A := ...             |k A
have hA : A := trivial_arg hA     |exact trivial_arg hA           |n A by TA from k
-/




----------------------------------------------------------------------------
-- 1.3.14 (PC) 		A ∨ B, A → C, B → C ⊢ C (Disjunction Rule, Proof by Cases)
----------------------------------------------------------------------------
/- -- 


Lean form               			|Gentzen-style derivation
have hAorB : A ∨ B := ...     |k A ∨ B
have hA : A := ...        		|l1 [A]PC1
.                     				|.
.                     				|.
.                   	 				|.	
exact hC			                |li C by PC1 from l1 to li-1
have hB : B :=...		          |m1 [B]PC2
.             				        |.
.             				        |.
.                   					|.
exact hC			                |mj C by PC2 from m1 to mj-1
				                      |n C by PC from k, l1 to li, m1 to mj
-/


/-
The Disjunction Rule is not logically independent of the rest of our list of rules (union
of basic and meta-rules). Nevertheless it is often added as basic because of its wide-spread applications.

The Disjunction Rule (Proof by Cases) is the most structural basic rule in Gentzen-style logic.
In Lean, this is naturally handled by the rcases tactic, which splits the proof into
the required sub-goals. Each sub-goal represents one "case" of the disjunction.

The bad news is: (PC) is the first of our basic rules which is not representable in
1:1 fashion, even if we restrict ourselves to only one application of a Meta-rule like
(CP), (IP) or (PEC). In the following example there is even no application of a meta-rule
at all, nevertheless it is not 1:1. (There are exceptions as we have observed with the PCs
dealing with (TA).)
-/

-- argument form (first hybrid)
example {P Q R : Prop} (h : (P ∧ R) ∨ (Q ∧ R)) : R := by {
  have h_disj : (P ∧ R) ∨ (Q ∧ R) := h   -- 1 [(P∧R)∨(Q∧R)] Pr
  rcases h_disj with hPR | hQR           -- Lean: PC with [P∧R]PC1 and [Q∧R]PC2
  have hPR : P∧R := hPR                  -- 2 [P∧R]PC1
  exact hPR.right                        -- 3 R by ∧-Elimination2 from 2
  have hQR : Q∧R := hQR                  -- 4 [Q∧R]PC2    
  exact hQR.right                        -- 5 R by ∧-Elimination2 from 4
                                         -- Lean: pending goal(s) silently closed
--------------------------------------------------------------------------------
                                         -- 6 R by PC from 1, 2-3, 4-5 
}
/-
Note that we have augmented our derivation not only by the Lean comment regarding
the silent closing of the goal, but also by the one introducing the rcases tactic.
We have not done so with the PCs in the (TA) section above. Logically it makes no
difference, since the rcases line introduces the cases "hPR | hQ" and in subsequent
lines the values (types) "P ∧ R" and "Q ∧ R" are available without being explicitly
constructed by "have"-statements.

We could have also commented the "rcases" with "[P∧R]PC1" (the first assumption) but the
Lean statement "PC with [P∧R]PC1 and [Q∧R]PC2" is more informative and we also want to
to give both assumptions in lines 2 and 4 the same logical form on both sides, Lean
and the derivation; so there is symmetry in both branches of the tree.

Note that the following proof for the corresponding formula only differs from the
previous in the first and in an additional last line; in other words the "heart"
of the proof remains the same - whether argument form or formula. This is typical
for Lean as we will show in the next section.
-/ 

--formula
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


--another argument form
example {P Q : Prop} (h1 : P ∨ Q) : Q ∨ P := by {
  have h1 : P ∨ Q := h1           -- 1 [P∨Q]Pr
  rcases h1 with h1P | h1Q        -- 2 [P]PC1
  exact Or.inr h1P                -- 3 Q∨P by ∨-Intro2 from 2
  have hQ : Q := h1Q              -- 4 [Q]PC2 
  exact Or.inl h1Q                -- 5 Q∨P by ∨-Intro1 from 4
-------------------------------------------------------------------
                                  -- 6 (Q ∨ P) by PC from 1,2-3,4-5 
}
/-
Again, we interpret the 'rcases h1 with h1P | h1Q statement' as [P]PC1. However, this is only half the truth, as [Q]PC2 simultaneously becomes available "under the hood". Moreover, introducing the PC1 assumption via 'rcases' while assigning the PC2 assumption to a 'have' statement just two lines later creates an asymmetric and somewhat artificial structure. In contrast, the following hybrid approach is more elegant and closer to a Gentzen-style derivation.

-/
--argument form hybrid 
example {P Q : Prop} (h1 : P ∨ Q) : Q ∨ P := by {
  have h1 : P ∨ Q := h1           -- 1 [P∨Q]Pr
  rcases h1 with h1P | h1Q        -- Lean: PC with [P]PC1, [Q]PC2
  have h1P : P := h1P             -- 2 [P]PC1
  exact Or.inr h1P                -- 3 Q∨P by ∨-Intro2 from 2
  have hQ : Q := h1Q              -- 4 [Q]PC2 
  exact Or.inl h1Q                -- 5 Q∨P by by ∨-Intro1 from 4
                                  -- Lean: pending goal(s) silently closed
--------------------------------------------------------------------------
                                  -- 6 (Q ∨ P) by PC from 1,2-3,4-5
}

--formula hybrid 
example {P Q : Prop} : (P ∨ Q) → (Q ∨ P) := by {
  intro h                         -- 1 [P∨Q]CP
  rcases h with hP | hQ           -- Lean: PC with case1: P, case2: Q
  have hP : P := hP               -- 2 [P]PC1
  have hQorP : Q∨P := Or.inr hP   -- 3 Q∨P by ∨-Intro1 from 2
  exact hQorP                     -- 4 Q∨P by PC1 from 2-3
  have hQ : Q := hQ               -- 5 [Q]PC2 
  have hQorP : Q∨P := Or.inl hQ   -- 6 Q∨P by ∨-Intro2 from 5
  exact hQorP                     -- 7 Q∨P by PC2 from 5-6
                                  -- Lean: pending goal(s) silently closed
---------------------------------------------------------------------
                                  -- 8 (P ∨ Q) → (Q ∨ P) by CP from 1-7
}
/-
Note that (PC) can also be formalized even closer to A ∨ B, A → C, B → C ⊢ C.
For this purpose we use the Or.elim Lemma and define it as a lemma before
our proof.

        Or.elim {a b c : Prop} (h : a ∨ b) (left : a → c) (right : b → c) : c
-/

def dis_prem {A B C : Prop} (hAB : A ∨ B) (hAC : A → C) (hBC : B → C) : C :=
  Or.elim hAB hAC hBC

#print dis_prem

-- argument form hybrid
example {P Q : Prop} (h1 : P ∨ Q) : Q ∨ P := by {
  apply dis_prem h1                 -- Lean: Splits goal into 2 subgoals
                                    -- P→Q∨P and Q→Q∨P 
  have h1 : P ∨ Q := h1             -- 1 [P∨Q]Pr
  intro hP                          -- 2 [P]CP1
  have h1 : Q ∨ P := Or.inr hP      -- 3 Q∨P by ∨-Intro2 from 2
  exact h1                          -- 4 P→Q∨P by CP1 from 2-3
  intro hQ                          -- 5 [Q]CP2
  have h2 : Q ∨ P := Or.inl hQ      -- 6 Q∨P by ∨-Intro1 from 5      
  exact h2                          -- 7 Q→Q∨P by CP2 from 5-6
                                    -- Lean: pending goal(s) silently closed
----------------------------------------------------------------------
                                    -- 8 Q∨P by dis_prem from 1,4,7
}
/-
Note that we did not use a proof by cases (PC) as we did before, but we naturally used
conditional subproofs (CP) to deal with the initially given subgoals P→Q∨P and Q→Q∨P.
"Naturally", because it also corresponds to Lean's use of "intro" (marking the start of a CP).
-/

-- formula
theorem or_comm_ {P Q : Prop} : (P ∨ Q) → (Q ∨ P) := by {
  intro h                         -- 1 [P∨Q]CP
  apply dis_prem h                -- Lean: Splits goal into 2 subgoals
                                  -- P→Q∨P and Q→Q∨P                       
  intro hP                        -- 2 [P]CP1
  have hQorP : Q∨P := Or.inr hP   -- 3 Q∨P by ∨-Intro2 from 2
  exact hQorP                     -- 4 P→Q∨P by CP1 from 2-3
  intro hQ                        -- 5 [Q]CP2 
  have hQorP : Q∨P := Or.inl hQ   -- 6 Q∨P by ∨-Intro1 from 5
  exact hQorP                     -- 7 Q→Q∨P by CP2 from 5-6
                                  -- Lean: pending goal(s) closed silently
  ----------------------------------------------------------------------
                                  -- 8 (Q ∨ P) by dis_prem from 1,4,7 
                                  -- 9 (Q ∨ P) → (Q ∨ P) by CP from 1-8
}
/-

The Disjunction Rule reminded us on or paradigm at the end of Section 1.3.1:

 "[ ... ] a fundamental methodological choice: one may either
(a) relax the strict 1:1 correspondence,
(b) refine the notion of an atomic Lean proof step, or
(c) adopt a hybrid derivation style."  

We have successfully avoided calling option (b) into question. This is because
we occasionally prefer to use "have" (atomic) while at other times applying "exact"
(non-atomic) — whichever is more suitable for preserving the 1:1 correspondence.
Consequently, we must now address (a) and (c). We need to partly relax the 1:1
correspondence, making it appropriate to adopt a hybrid derivation style. This
represents a paradigm shift. In the following section, we will specify exactly
when and why the 1:1 correspondence breaks down.


------------------------------------------------------------------------
1.4 META-RULES
------------------------------------------------------------------------


Let B, A1, ... ,An and C be propositional schema variables;

------------------------------------------------------------------------
1.4.1 (IP) Indirect Proof
------------------------------------------------------------------------

If

          ¬B, A1, ... ,An ⊢ C ∧ ¬C
          
is a Rule of Inference, then so is
  
              A1, ... ,An ⊢ B.

Schema:

 ¬B, A1, ... ,An ⊢ C ∧ ¬C
---------------------------
      A1, ... ,An ⊢ B


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form                             |Gentzen-style derivation
by_contra hnP                         |k  [¬B]IP
.                                     |
.                                     |
.                                     |
have cont : C ∧ ¬C := And.intro ...   |l C ∧ ¬C by ∧-Intro from 2 contradicting
                                      |  propositions from k to l-1                         
contradiction                         |B by IP from k-l   

/-
We have already seen that a single application of (IP), without additional applications of meta-rules, sometimes preserves the 1:1 correspondence. Here is an example in which both the proof of the argument form and the proof of the corresponding formula preserve the 1:1 correspondence.
-/

-/
--argument form
example {P Q : Prop} (h: P ∨ Q) : (¬P → Q) := by {
  have h : P ∨ Q := h                    -- 1 [P∨Q]Pr    
  by_contra hnnPQ                        -- 2 [¬(¬P→Q)]IP
  have h4 : ¬P ∧ ¬Q := Classical.not_imp.mp hnnPQ -- 3 ¬P∧¬Q by Th ¬(a→b)→(a∧¬b) from 2
  have h5 : ¬Q := h4.right               -- 4 ¬Q by ∧-Elimination2 from 3 
  have h6 : P := Or.resolve_right h h5   -- 5 P by DS2 from 1,4
  have h7 : ¬P := h4.left                -- 6 ¬P by ∧-Elimination1 from 3
  have cont : P ∧ ¬P := And.intro h6 h7  -- 7 P∧¬P by ∧-Intro from 5,6
  contradiction                          -- 8 (¬P → Q) by IP from 2-7
}
 
--formula
example {P Q : Prop} : (P ∨ Q) → (¬P → Q) := by {
  by_contra hnPQ                        -- 1 [(P∨Q)→(¬P→Q)]IP
  have h1 : (P ∨ Q) ∧ ¬(¬P → Q) := Classical.not_imp.mp hnPQ -- 2 (P∨Q)∧¬(¬P→Q) by
                                                             --   Th [¬(a→b)→(a∧¬b) from 1 
  have h2 : (P ∨ Q) := h1.left          -- 3 P∨Q by ∧-Elimination1 from 2
  have h3 : ¬(¬P → Q) := h1.right       -- 4 ¬(¬P → Q) by ∧-Elimination2 from 2
  have h4 : ¬P ∧ ¬Q := Classical.not_imp.mp h3 -- 5 ¬P∧¬Q by Th ¬(a→b)→(a∧¬b) from 4
  have h5 : ¬Q := h4.right              -- 6 ¬Q by ∧-Elimination2 from 5
  have h6 : P := Or.resolve_right h2 h5 -- 7 P by DS2 from 3,6
  have h7 : ¬P := h4.left               -- 8 ¬P by ∧-Elimination1 from 5               
  have cont : P ∧ ¬P := And.intro h6 h7 -- 9 P∧¬P by ∧-Intro from 7,8
  contradiction                         --10 (P ∨ Q) → (¬P → Q) by IP from 1-9
}

/-
However, as soon as another meta-rule is applied, the 1:1 correspondence breaks down: Lean finishes first, while the derivation continues.
-/


--formula, nested CPs and IP
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

/-
We call this process Lean's "implicit structural closure": once the boundary of open goals is empty, Lean silently discharges all remaining undischarged assumptions introduced by tactics such as intro.

One can see Lean's dynamic tactic management in comparison to a derivation sequence. Every
time the cursor is positioned at the end of the next Lean statement, you can see the changes
done to the tactic state in the Lean invo-view:


Lean code                                            Tactic state (starting from "|" cursor position)

example {P Q : Prop} : (P ∨ Q) → (¬P → Q) := by|     1 goal: [ ⊢ (P ∨ Q) → (¬P → Q) ]              

intro h1|                                            1 goal: [ P ∨ Q ⊢ ¬P → Q ] 

intro h2|                                            1 goal: [ P ∨ Q, ¬P ⊢ Q ] 

by_contra hnQ|                                       1 goal: [ P ∨ Q, ¬P, ¬Q ⊢ False ] 

have h3 : P := Or.resolve_right h1 hnQ|              1 goal: [ P ∨ Q, ¬P, ¬Q, P ⊢ False ]

have cont : P ∧ ¬P := And.intro h3 h2|               1 goal: [ P ∨ Q, ¬P, ¬Q, P, P ∧ ¬P ⊢ False ]

contradiction|                                       No goals: [ ]
-------------------------------------------------------------------------------------------------

The implicit structural closure starts when there is no goal left to be solved. Once the final goal is solved (here: the contradiction / False), the assumptions introduced by the previous goal-changing steps (intro h1 and intro h2) are discharged backwards, one after the other: first h2, then h1.

In general, once the final goal in every branch has been solved, Lean's implicit structural closure starts and each assumption not yet discharged is discharged backwards, one after the other.

Now we can say that we have so far given examples for all basic rules and the first meta-rule (IP)
of our system of Natural Deduction showing that a 1:1 correspondence between Lean lines and derivation lines can be maintained. The 1:1 correspondence only breaks down after Lean's implicit structural closure starts, or when branching tactics are used (like "rcases" or "apply dis_prem" which is needed to change Lean's tactic). With "rcases" one could use the branching statement as "first case" though, but we don't recommend it for the loss of expliciteness.
-/



/-
------------------------------------------------------------------
1.4.2 (CP) Conditional Proof
------------------------------------------------------------------

If

        A1, ... ,An, B ⊢ C
        
is a rule of inference, then so is

        A1, ... ,An ⊢ B → C.


Schema
A1, ... ,An, B ⊢ C
-------------------
A1, ... ,An ⊢ B → C


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form                             |Gentzen-style derivation                            
intro hB                              |k [B]CP 
.                                     |
.                                     |
.                                     |
have hC : C := by ...                 |n C by ...
exact hC                              |n+1 B → C by CP from k-n

-/

--Examples

--formula
theorem imp_imp_and {P Q : Prop} : P → (Q → (P ∧ Q)) := by {
  intro hP    -- 1 [P]CP1
  intro hQ    -- 2 [Q]CP2
  have h1 : (P ∧ Q) := And.intro hP hQ -- 3 P∧Q by ∧-Intro from 1, 2
  exact h1    -- 4 Q→(P∧Q) by CP2 from 2-3
}             -- Lean: pending goal(s) closed
--------------------------------------------------------------------
              -- 5 P→(Q→(P∧Q)) by CP1 from 1-4


/-
There is one way to preserve the 1:1 correspondence in a purely formal sense. The keyword
"done" succeeds iff there are no remaining goals. When placed at the end of a proof,
'done' succeeds only if the proof is complete. In the Lean 4 Web editor, the keyword is
underlined in red when placed below a valid proof. This happens because the linter reports
it as an unused tactic. To suppress this specific warning, one has to set:

set_option linter.unusedTactic false.
-/
set_option linter.unusedTactic false
theorem five_imp {P Q : Prop} : P → P → P → P → (Q → P) := by {
  intro h1                        -- 1 [P]CP1
  intro h2                        -- 2 [P]CP2
  intro h3                        -- 3 [P]CP3
  intro h4                        -- 4 [P]CP4
  intro h5                        -- 5 [Q]CP5
  have hP : P := trivial_arg h1   -- 6 P by TA from 1
  exact hP                        -- 7 Q → P by CP5 from 5-6
                                  -- Lean: pending goal(s) closed
-----------------------------------------------------------------------------
  done                            -- 8 P → (Q → P) by CP4 from 4-7
  done                            -- 9 P → P → (Q → P) by CP3 from 3-8
  done                            --10 P → P → P → (Q → P) by CP2 from 2-9
  done                            --11 P → P → P → P → (Q → P) by CP1 from 1-10
}
/-
We dismiss this solution, since it is misleading: several occurrences of 'done' in a row 
have no real effect and merely suggest a correspondence to the derivation that does not
actually exist.



----------------------------------------------------------------------------
1.4.3 (PEC) Proof by Exhaustive Cases
(also called Proof by Exhaustion; German: „Vollständige Fallunterscheidung“)
----------------------------------------------------------------------------

If

          A, B1, ... ,Bn ⊢ C
 
and
  
          ¬A, B1, ... ,Bn ⊢ C,
   
are Rules of Inference, then so is
    
          B1, ... ,Bn ⊢ C.



Schema

A, B1, ... ,Bn ⊢ C   ¬A, B1, ... ,Bn ⊢ C
----------------------------------------
          B1, ... ,Bn ⊢ C


Simplified comparison between Gentzen-style derivations and Lean proofs

Lean form                             |Gentzen-style derivation   
                                      |
by_cases hA : A                       |k [A]PEC
.                                     |
.                                     |
.                                     |
exact hC                              |l C by ...
have hnA : ¬A := hA                   |l+1 [¬A]PEC
.                                     |
.                                     |
.                                     |
have hC : C :=                        |m C by ...
exact hC                              |m+1 C by PEC from k-m



-/

--Examples

-- argument form
example  (P Q : Prop) (h1 : P → Q) : (¬P ∨ Q) := by {
  have h1 : P → Q := h1             -- 1 [P→Q]Pr
  by_cases hP : P                   -- 2 [P]PEC1
  have hQ : Q := h1 hP              -- 3 Q by Modus Ponens from 1,2
  exact Or.inr hQ                   -- 4 ¬P ∨ Q by ∨-Intro2 from 3
  have hnP : ¬P := hP               -- 5 [¬P]PEC2
  have goal2 : ¬P ∨ Q := Or.inl hP  -- 6 ¬P ∨ Q by ∨-Intro1 from 5
  exact goal2                       -- 7 ¬P ∨ Q by PC from 2-6
}

/- In the previous section we explicitly recommended to use an unnumbered Lean comment
in the derivation if there is a branching statemant (like rcases) in the Lean code. In the following hybrid version, the introduction of the "by_cases" tactic is accompanied by an explanatory Lean comment and a closure remark at the end.  

-/
-- argument form (hybrid)
example  (P Q : Prop) (h1 : P → Q) : (¬P ∨ Q) := by {
  have h1 : P → Q := h1             -- 1 [P→Q]Pr
  by_cases hP : P                   -- Lean: PEC with case1: P, case2: ¬P
  have hP : P := hP                 -- 2 [P]PEC1
  have hQ : Q := h1 hP              -- 3 Q by Modus Ponens from 1,2
  exact Or.inr hQ                   -- 4 ¬P ∨ Q by ∨-Intro2 from 3
  have hnP : ¬P := hP               -- 5 [¬P]PC2
  have goal2 : ¬P ∨ Q := Or.inl hP  -- 6 ¬P ∨ Q by ∨-Intro1 from 5
  exact goal2                       -- 7 ¬P ∨ Q by PEC from 2-6
                                    -- Lean: pending goal(s) closed
}

-- formula
example (P Q : Prop) : (P → Q) → (¬P ∨ Q) := by {
  intro h                           -- 1 [P→Q]CP 
  by_cases hP : P                   -- Lean: PEC with case1: P, case2: ¬P
  have hP : P := hP                 -- 2 [P]PEC1
  have hQ : Q := h hP               -- 3 Q by Modus Ponens from 1,2
  exact Or.inr hQ                   -- 4 ¬P ∨ Q by ∨-Intro2 from 3
  have hnP : ¬P := hP               -- 5 [¬P]PEC2
  have goal2 : ¬P ∨ Q := Or.inl hP  -- 6 ¬P ∨ Q by ∨-Intro1 from 5
  exact goal2                       -- 7 ¬P ∨ Q by PEC from 2-6
                                    -- Lean: pending goal(s) closed
-------------------------------------------------------------------
                                    -- 8 (P → Q) → (¬P ∨ Q) by CP from 1-7
}

/-
This concludes our considerations on how to establish a basis of rules for our Lean–Gentzen style of propositional logic theorem proving.
-/


/-!
--------------------------------------------------------------------
## 1.4 Preliminary Conclusion
--------------------------------------------------------------------

This first part of the investigation evaluates the extensional 1:1 correspondence 
between classic Gentzen-style Natural Deduction derivations and formal Lean 4 
tactic proofs. The structural alignment yields the following insights:

1. **Success of Local Rules:** Success of Local Rules: Standard linear inference rules -
  such as Modus Ponens (MP), Modus Tollens (MT), Disjunctive Syllogisms (DS1/DS2), and
  Conjunction rules (∧E/∧I) — map perfectly onto explicit Lean expressions. Using "have"
  structures for intermediate steps preserves exact granularity. To isolate the behavior
  of these basic rules, our analysis is restricted to derivations containing at most a
  single application of any meta-rule (IP, CP, or PC). Even within this scope, a notable
  exception is the disjunction rule (Proof by Cases, PC: A ∨ B, A → C, B → C ⊢ C), for 
  which we provide a counterexample that cannot be represented in a 1:1 fashion.
  Consequently, both this limitation and the challenges of nested meta-rules lead us 
  directly to the problem of Implicit Structural Closure.

2. **The Limit of Implicit Structural Closure:** Lean’s proof engine operates on a
  goal-driven mechanism. When a final target type is synthesized, closing commands like
  exact or contradiction immediately terminate subgoals internally. This automation
  introduces a structural boundary: Lean obscures the distinction between constructing
  the final proposition and discharging the surrounding meta-rule context (e.g., CP or IP).

3. **Branching and Asymmetry Boundaries:** The absolute 1:1 mapping encounters a 
  conceptual bottleneck in rules that trigger structural splits (such as Disjunction
  Elimination via `rcases` or `by_cases`). Forcing a strict line-by-line derivation
  creates a structural asymmetry, wherein the tactic command must simultaneously serve
  as both the structural announcement and the implicit, immediate assumption of the first
  branch.

**The Hybrid Derivation Paradigm:**
To escape artificial proof constructs while maintaining absolute explicitness, we 
propose a *Hybrid Gentzen-Lean Style*. By embedding unnumbered, metadata-rich Lean 
comments alongside the strictly numbered Gentzen sequence, the proof architecture 
remains readable for human logicians and transparent for machine analysis. This 
coexistence preserves the deductive linearity of natural deduction without hiding 
Lean’s internal goal transformations.
-/

-- 1.6 Derived Rules
--tbd
/-
1.6.1 (EqUI) A → B, B → A ⊢ A ↔ B (Equivalence Intro)
1.6.2 (EQUE1) A ↔ B ⊢ A → B (Equivalence Elimination 1)
1.6.3 (EQUE2) A ↔ B ⊢ B → A (Equivalence Elimination 2)
1.6.4 --Iff.or------∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
1.6.5 Proofs by Equivalence Transformation
-/ 

theorem and_equi_or_ {P Q : Prop} : (P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := by {
  have th1 : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := not_and_or
  -- 1 [¬(P∧Q)↔¬P∨¬Q]Th1
  -- Remark: Now we apply negation on both sides of "↔" of Th1:
  have th2 : ¬¬(P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := Iff.not th1
  -- 2 ¬¬(P∧Q)↔¬(¬P∨¬Q) by Modus Ponens from
  --   [(a↔b)↔(¬a↔¬b)]Th2 (setting a := ¬(P∧Q),
  --   b := ¬P∨¬Q) and from 1
  have nn : (P ∧ Q) ↔ ¬¬(P ∧ Q) := ⟨not_not_intro, of_not_not⟩
  -- 3  (P∧Q) ↔ ¬¬(P∧Q) by ∧-Intro from [A→¬¬A]Th3,  [¬¬A→A]Th4 (setting A:=(P∧Q)
  have th3 : (P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := Iff.trans nn th2
  -- 4 (P∧Q) ↔ ¬(¬P∨¬Q) by [(A↔B)∧(B↔C)→(A↔B)]Th5 (setting A:=P∧Q, B:=¬¬(P∧Q), C:=¬(¬P ∨ ¬Q)) from 3,2
  exact th3
}








