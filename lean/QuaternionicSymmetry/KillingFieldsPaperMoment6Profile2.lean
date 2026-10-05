import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile1
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_2 : P :=
  C (193208 / 308706739417951875 : ℚ) * p6
    + C (354182 / 198944343180457875 : ℚ) * p1 * p5
    + C (522059182 / 721571132715520712625 : ℚ) * p2 * p4
    + C (105998254 / 42445360747971806625 : ℚ) * p1 ^ 2 * p4
    + C (1169004119 / 4638671567456918866875 : ℚ) * p3 ^ 2
    + C (25247999027 / 10823566990732810689375 : ℚ) * p1 * p2 * p3
    + C (80470643153 / 32470700972198432068125 : ℚ) * p1 ^ 3 * p3
    + C (903654121 / 3607855663577603563125 : ℚ) * p2 ^ 3
    + C (33280306967 / 14431422654310414252500 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (48740924129 / 21647133981465621378750 : ℚ) * p1 ^ 4 * p2
    + C (7751023289 / 18554686269827675467500 : ℚ) * p1 ^ 6

theorem moment6_2_eq : moment 6 2 = expanded6_2 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_2, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
