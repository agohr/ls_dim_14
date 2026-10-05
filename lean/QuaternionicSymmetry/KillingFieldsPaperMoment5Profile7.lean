import QuaternionicSymmetry.KillingFieldsPaperMoment5Profile5
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded5_7 : P :=
  C (969659627 / 13840653034333125 : ℚ) * p5
    + C (39602918669 / 160551575198264250 : ℚ) * p1 * p4
    + C (147285409 / 1926618902379171 : ℚ) * p2 * p3
    + C (106360931387 / 240827362797396375 : ℚ) * p1 ^ 2 * p3
    + C (2142793316 / 11467969657018875 : ℚ) * p1 * p2 ^ 2
    + C (43809695801 / 68807817942113250 : ℚ) * p1 ^ 3 * p2
    + C (350821986176 / 1204136813986981875 : ℚ) * p1 ^ 5

theorem moment5_7_eq : moment 5 7 = expanded5_7 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded5_7, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
