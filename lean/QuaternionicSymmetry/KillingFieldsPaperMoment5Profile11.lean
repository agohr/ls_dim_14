import QuaternionicSymmetry.KillingFieldsPaperMoment5Profile8
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded5_11 : P :=
  C (873238151 / 13840653034333125 : ℚ) * p5
    + C (42185170327 / 160551575198264250 : ℚ) * p1 * p4
    + C (856130581 / 18525181753645875 : ℚ) * p2 * p3
    + C (6216198559 / 10470754904234625 : ℚ) * p1 ^ 2 * p3
    + C (14654952259 / 160551575198264250 : ℚ) * p1 * p2 ^ 2
    + C (51005084233 / 68807817942113250 : ℚ) * p1 ^ 3 * p2
    + C (1568229944581 / 2408273627973963750 : ℚ) * p1 ^ 5

theorem moment5_11_eq : moment 5 11 = expanded5_11 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded5_11, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
