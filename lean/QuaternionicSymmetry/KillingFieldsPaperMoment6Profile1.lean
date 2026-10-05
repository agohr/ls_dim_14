import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile0
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_1 : P :=
  C (-16 / 12348269576718075 : ℚ) * p6
    + C (-688 / 464203467421068375 : ℚ) * p1 * p5
    + C (17008 / 25902553482095615325 : ℚ) * p2 * p4
    + C (19364 / 25902553482095615325 : ℚ) * p1 ^ 2 * p4
    + C (3067 / 4757611864058378325 : ℚ) * p3 ^ 2
    + C (3083 / 740072956631303295 : ℚ) * p1 * p2 * p3
    + C (7369 / 2561791003723742175 : ℚ) * p1 ^ 3 * p3
    + C (50684 / 77707660446286845975 : ℚ) * p2 ^ 3
    + C (35263 / 7970016456029420100 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (6491 / 1918707665340415950 : ℚ) * p1 ^ 4 * p2
    + C (2484047 / 4662459626777210758500 : ℚ) * p1 ^ 6

theorem moment6_1_eq : moment 6 1 = expanded6_1 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_1, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
