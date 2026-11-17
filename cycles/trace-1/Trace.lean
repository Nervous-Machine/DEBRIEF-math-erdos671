-- Worked examples for the reading guide (cycle 1, trace/DEFINITIONAL-TRACE.md, Part D).
--
-- WRITTEN BUT NOT RUN. No Lean, lake or claimant code was executed in cycle 1. Nothing below is a result until a
-- later cycle runs it and pins the transcript. Some tactic lines may need adjusting; the statements are what matter.
--
-- How to run: put QuietMethod's pinned file (sha256 98375fe5..., or Price's decoded text, sha256 3854ae85...) in a Lean
-- project on Lean v4.33.0-rc1 with Mathlib at tag v4.33.0-rc1 (79d0395a), as module `Erdos671_square_samples`, then
-- `lake env lean cycles/trace-1/Trace.lean`.
import Erdos671_square_samples

open Filter Topology Erdos671

-- 1. `Interval` in the statement is the claimants' abbreviation, not Mathlib's root-level `Interval` type.
example : Erdos671.Interval = Set.Icc (-1 : ℝ) 1 := rfl

-- 2. A concrete row: the two nodes -1 and 1.
def row2 : Row 2 where
  ι := Fin 2
  fintypeι := inferInstance
  decidableEqι := inferInstance
  card_ι := by simp
  node := ⟨![⟨-1, by norm_num, by norm_num⟩, ⟨1, by norm_num, by norm_num⟩], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all <;> norm_num at h⟩

-- 2a. Fundamental polynomials at x = 0 are 1/2 and 1/2; the Lebesgue function at 0 is 1 (classical value for two nodes).
example : fundamental row2 (0 : Fin 2) 0 = 1 / 2 := by
  rw [fundamental_eq_prod]; simp [row2]; norm_num
example : lebesgue row2 0 = 1 := by
  simp [lebesgue, fundamental_eq_prod, row2, Fin.sum_univ_two]; norm_num

-- 3. Three equispaced nodes -1, 0, 1: the Lebesgue function at x = 1/2 is 1/8 + 3/4 + 3/8 = 5/4 (classical value).
def row3 : Row 3 where
  ι := Fin 3
  fintypeι := inferInstance
  decidableEqι := inferInstance
  card_ι := by simp
  node := ⟨![⟨-1, by norm_num, by norm_num⟩, ⟨0, by norm_num, by norm_num⟩, ⟨1, by norm_num, by norm_num⟩], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all <;> norm_num at h⟩
example : lebesgue row3 (1 / 2) = 5 / 4 := by
  simp [lebesgue, fundamental_eq_prod, row3, Fin.sum_univ_three]; norm_num

-- 4. The claimants' own sanity lemmas linking their definitions to Mathlib's Lagrange interpolation.
#check @fundamental_at_node            -- fundamental X i (node j) = if i = j then 1 else 0
#check @interpolant_at_node            -- interpolant X f (node i) = f (node i)
#check @lebesgue_at_node               -- lebesgue X (node i) = 1
#check @interpolant_eq_eval_interpolate -- interpolant = evaluation of Mathlib's Lagrange.interpolate
#check @interpolant_polynomial         -- reproduces polynomials of degree < n
#check @Lagrange.natDegree_basis       -- degree of the basis polynomial is (#nodes - 1)

-- 5. "For all A and N there is n ≥ N with A ≤ u n" is "A ≤ u n frequently, for every A".
example (u : ℕ → ℝ) :
    (∀ A : ℝ, ∀ N : ℕ, ∃ n ≥ N, A ≤ u n) ↔ ∀ A : ℝ, ∃ᶠ n in atTop, A ≤ u n := by
  simp only [Filter.frequently_atTop]

-- 6. The row sizes: X n has n + 1 nodes, so n = 0, 1, 2, ... covers rows of size 1, 2, 3, ...
example (X : ∀ n : ℕ, Row (n + 1)) (n : ℕ) : (nodeSet (X n)).card = n + 1 := card_nodeSet _

-- 7. The statement, the definitions behind it, and the axioms of the main theorem.
#check @erdos_671
#print Row
#print fundamental
#print interpolant
#print lebesgue
#print nodeSet
#print Lagrange.basis
#print Lagrange.basisDivisor
#print axioms erdos_671
