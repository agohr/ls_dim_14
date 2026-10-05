import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile8
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_9 : P :=
  C (-14492146 / 1513708259641875 : ℚ) * p6
    + C (-4240149674 / 172019544855283125 : ℚ) * p1 * p5
    + C (1113987421223 / 323511424024502463750 : ℚ) * p2 * p4
    + C (-24748337803 / 13938133914887861250 : ℚ) * p1 ^ 2 * p4
    + C (23049109687286 / 5337938496404290651875 : ℚ) * p3 ^ 2
    + C (678214373038141 / 14488690204525931769375 : ℚ) * p1 * p2 * p3
    + C (95417820991 / 1154148864087414195 : ℚ) * p1 ^ 3 * p3
    + C (378436066697509 / 81136665145345217908500 : ℚ) * p2 ^ 3
    + C (388573590251557 / 4270350797123432521500 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (11241873021775567 / 57954760818103727077500 : ℚ) * p1 ^ 4 * p2
    + C (609007408805503 / 7117251328539054202500 : ℚ) * p1 ^ 6

theorem moment6_9_eq : moment 6 9 = expanded6_9 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_9, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
