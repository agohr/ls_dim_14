import QuaternionicSymmetry.KillingFieldsPaperMoment4Profile5
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded4_6 : P :=
  C (-334116989 / 39900981720600 : ℚ) * p4
    + C (-774965201 / 34713854096922 : ℚ) * p1 * p3
    + C (3293970661 / 210386994526800 : ℚ) * p2 ^ 2
    + C (3572177153 / 13300327240200 : ℚ) * p1 ^ 2 * p2
    + C (2694164944087 / 6942770819384400 : ℚ) * p1 ^ 4

theorem moment4_6_eq : moment 4 6 = expanded4_6 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded4_6, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
