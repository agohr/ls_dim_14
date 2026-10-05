import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile6
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_7 : P :=
  C (31313920468 / 15620561014548364875 : ℚ) * p6
    + C (3549530112046 / 480450588780805768125 : ℚ) * p1 * p5
    + C (1900784969443 / 929383618937590677861 : ℚ) * p2 * p4
    + C (3076765290303977 / 232345904734397669465250 : ℚ) * p1 ^ 2 * p4
    + C (1140937876523773 / 1643017469193240662647125 : ℚ) * p3 ^ 2
    + C (4500366384113917 / 547672489731080220882375 : ℚ) * p1 * p2 * p3
    + C (1154206360097954 / 71435542138836550549875 : ℚ) * p1 ^ 3 * p3
    + C (1523041253342779 / 2555804952078374364117750 : ℚ) * p2 ^ 3
    + C (13182979144078192 / 1277902476039187182058875 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (69095392539000782 / 3833707428117561546176625 : ℚ) * p1 ^ 4 * p2
    + C (326322859894693034 / 57505611421763423192649375 : ℚ) * p1 ^ 6

theorem moment6_7_eq : moment 6 7 = expanded6_7 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_7, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
