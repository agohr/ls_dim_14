import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile3
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_5 : P :=
  C (14636 / 46406895468058125 : ℚ) * p6
    + C (245442094 / 160150196260268589375 : ℚ) * p1 * p5
    + C (215275190939 / 580864761835994173663125 : ℚ) * p2 * p4
    + C (351580238623 / 105611774879271667938750 : ℚ) * p1 ^ 2 * p4
    + C (2528652127 / 43930948374150819856875 : ℚ) * p3 ^ 2
    + C (440365403099 / 248942040786854645855625 : ℚ) * p1 * p2 * p3
    + C (737002471774 / 149365224472112787513375 : ℚ) * p1 ^ 3 * p3
    + C (7749592789 / 46469180946879533893050 : ℚ) * p2 ^ 3
    + C (439313673826 / 116172952367198834732625 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (401413818802 / 47097142851567095161875 : ℚ) * p1 ^ 4 * p2
    + C (17913863855984 / 5227782856523947562968125 : ℚ) * p1 ^ 6

theorem moment6_5_eq : moment 6 5 = expanded6_5 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_5, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
