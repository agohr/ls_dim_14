import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile7
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_8 : P :=
  C (-634481966 / 46908591635280375 : ℚ) * p6
    + C (-153015915146 / 5931488750380318125 : ℚ) * p1 * p5
    + C (11838210407 / 1987850283911241750 : ℚ) * p2 * p4
    + C (1233846340169 / 220651381514147834250 : ℚ) * p1 ^ 2 * p4
    + C (12762554054 / 2008134470481764625 : ℚ) * p3 ^ 2
    + C (87984316689679 / 1560320483564331113625 : ℚ) * p1 * p2 * p3
    + C (115232496477473 / 1560320483564331113625 : ℚ) * p1 ^ 3 * p3
    + C (7310393269759 / 1180783068643277599500 : ℚ) * p2 ^ 3
    + C (417697450677401 / 4854330393311252353500 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (5803259657263619 / 43688973539801271181500 : ℚ) * p1 ^ 4 * p2
    + C (9317435975046113 / 218444867699006355907500 : ℚ) * p1 ^ 6

theorem moment6_8_eq : moment 6 8 = expanded6_8 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_8, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
