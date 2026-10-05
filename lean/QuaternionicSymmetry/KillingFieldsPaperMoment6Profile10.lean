import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile9
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_10 : P :=
  C (-370261504423 / 31241122029096729750 : ℚ) * p6
    + C (-581028610961 / 22878599465752655625 : ℚ) * p1 * p5
    + C (25130338083853 / 4917373645172437449000 : ℚ) * p2 * p4
    + C (7621606992689 / 2107445847931044621000 : ℚ) * p1 ^ 2 * p4
    + C (2023696212960901 / 365114993154053480588250 : ℚ) * p3 ^ 2
    + C (19099394750624789 / 365114993154053480588250 : ℚ) * p1 * p2 * p3
    + C (29818934416038587 / 365114993154053480588250 : ℚ) * p1 ^ 3 * p3
    + C (14410842961877431 / 2920919945232427844706000 : ℚ) * p2 ^ 3
    + C (780407867855951 / 9272761730896596332400 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (92203706702415787 / 584183989046485568941200 : ℚ) * p1 ^ 4 * p2
    + C (100199390051906533 / 1622733302906904358170000 : ℚ) * p1 ^ 6

theorem moment6_10_eq : moment 6 10 = expanded6_10 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_10, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
