import QuaternionicSymmetry.KillingFieldsPaperDensity
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def profile : Fin 12 → List ℕ := ![
  [1, 4],
  [1, 1],
  [1, 1, 4],
  [1, 4, 4, 4],
  [1, 16, 16, 16],
  [1, 1, 1, 1, 4],
  [1, 16, 16, 16, 16],
  [1, 1, 1, 1, 4, 4, 16],
  [1, 1, 1, 1, 1, 1, 1, 16, 16],
  [1, 1, 1, 1, 1, 1, 1, 4, 16, 16],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 16, 16],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 16]]

theorem profiles_admissible (j : Fin 12) :
    (profile j).length ≤ 14 ∧ (profile j) ≠ [] ∧ ∀ a ∈ profile j, 0 < a := by
  fin_cases j <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, profile]
  all_goals simp

/-- The rank is fixed independently of the ambient manifold dimension. -/
def moment (k : ℕ) (j : Fin 12) : P :=
  H2WitnessThirteen.embed (FiniteTypeCSchurSix.orbital 14 k (profile j))


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
