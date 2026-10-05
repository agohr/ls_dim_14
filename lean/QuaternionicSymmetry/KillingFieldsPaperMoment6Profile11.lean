import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile10
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_11 : P :=
  C (73299676 / 41521959102999375 : ℚ) * p6
    + C (1831596722 / 231096964300531875 : ℚ) * p1 * p5
    + C (1244134782619 / 1276625850188998183875 : ℚ) * p2 * p4
    + C (322972992709 / 19197381205849596750 : ℚ) * p1 ^ 2 * p4
    + C (42521724554237 / 57448163258504918274375 : ℚ) * p3 ^ 2
    + C (5762891843987 / 1007862513307103829375 : ℚ) * p1 * p2 * p3
    + C (116064085614254 / 4419089481423455251875 : ℚ) * p1 ^ 3 * p3
    + C (642671857 / 7383608156095998750 : ℚ) * p2 ^ 3
    + C (35675204274977 / 6383129250944990919375 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (2256359567402 / 91623864846100348125 : ℚ) * p1 ^ 4 * p2
    + C (4816061958151 / 310530612208134693375 : ℚ) * p1 ^ 6

theorem moment6_11_eq : moment 6 11 = expanded6_11 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_11, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
