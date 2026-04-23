import Mathlib.Tactic
import Mathlib.Logic.Basic
open Classical



--Basic Rules---------------------------------------------
/-Abbr. Derivation Rule Names
-- (MP) A, A → B ⊢ B (Modus Ponens)
-- (MT) A → B, ¬B ⊢ A (Modus Tollens)
-- (DS1) A ∨ B, ¬A ⊢ B (Disjunctive Syllogism 1)
--(DS2) A ∨ B, ¬ B ⊢ A (Disjunctive Syllogism 2)
--(∧-Elim1) A ∧ B ⊢ A (∧-Elimination 1, Simplification 1)
--(∧-Elim2) A ∧ B ⊢ B (∧-Elimination 2, Simplification 2)
--(∨-Intro1) A ⊢ A ∨ B (∨-Intro 1, Addition 1)
--(∨-Intro2) B ⊢ A ∨ B (∨-Intro 2, Addition 2)
--(DNI) A ⊢ ¬¬A (Double Negation Intro)
--(DNE) ¬¬A ⊢ A (Doppelte Negation Elimination)
--(DIS) A → C, B → C ⊢ A ∨ B → C (Disjunction)
--(TA) A → A (Trivial Argument)
--(ECQ) A, ¬A ⊢ B (Ex Contradictione Quodlibet)
--Basic Rules---------------------------------------------

--Meta Rules---------------------------------------------
(IP) Indirect Proof
(CP) Conditional Proof
(PC) Proof by Cases (Exhaustion)
--Meta Rules---------------------------------------------
-/

theorem and_equi_or_ {P Q : Prop} : (P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := by {
  have th1 : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by exact not_and_or
                                  -- 1 [¬(P∧Q)↔¬P∨¬Q]Th1
  -- Remark: Now we apply negation on both sides of "↔" of Th1:
  have th2 : ¬¬(P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := Iff.not th1 
                                  -- 2 ¬¬(P∧Q)↔¬(¬P∨¬Q) by Modus Ponens from
                                  --   [(a↔b)↔(¬a↔¬b)]Th2 (setting a := ¬(P∧Q),
                                  --   b := ¬P∨¬Q) and from 1
  have nn : (P ∧ Q) ↔ ¬¬(P ∧ Q) := ⟨not_not_intro, of_not_not⟩
                                  -- 3  (P∧Q) ↔ ¬¬(P∧Q) by ∧-Intro from [A→¬¬A]Th3,
                                  --  [¬¬A→A]Th4 (setting A:=(P∧Q)
  have th3 : (P ∧ Q) ↔ ¬(¬P ∨ ¬Q) := Iff.trans nn th2
                                  -- 4 (P∧Q) ↔ ¬(¬P∨¬Q) by [(A↔B)∧(B↔C)→(A↔B)]Th5
                                  -- (setting A:=P∧Q, B:=¬¬(P∧Q), C:=¬(¬P ∨ ¬Q)) from 3,2
  exact th3
}



/-
(MP) A, A → B ⊢ B (Modus Ponens)


as derivation (k,l,m,n ∈ ℕ)
.
.
.
k A by ...
.
.
.
l A → B by ...
.
.
.
n B by MP from k,l
where k,l<n; order of k,l irrelevant

Numbererd Lean notation
1) using "have"                           |2) using "apply"
.                                         |.
.                                         |.
.                                         |.
k hA : A := ...                           |k hA : A := ...
.                                         |.
.                                         |.
.                                         |.
l hImp : A → B := ....                    |l hImp : A → B := ...
.                                         |.
.                                         |.
.                                         |.
n have hB : B := hImp hA                  |n apply hImp hA
where k,l<n; order of k,l irrelevant      |where k,l<n; order of k,l irrelevant
-/                                         |

