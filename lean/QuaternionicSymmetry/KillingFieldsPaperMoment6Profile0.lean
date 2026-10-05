import QuaternionicSymmetry.KillingFieldsPaperMoment5Profile11
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_0 : P :=
  C (3319 / 3528077021919450 : ℚ) * p6
    + C (997 / 530518248481221 : ℚ) * p1 * p5
    + C (2546041 / 2691174387750193800 : ℚ) * p2 * p4
    + C (55774267 / 29602918265252131800 : ℚ) * p1 ^ 2 * p4
    + C (25475651 / 66606566096817296550 : ℚ) * p3 ^ 2
    + C (1408471 / 672793596937548450 : ℚ) * p1 * p2 * p3
    + C (88487327 / 66606566096817296550 : ℚ) * p1 ^ 3 * p3
    + C (42246419 / 177617509591512790800 : ℚ) * p2 ^ 3
    + C (11313229 / 8457976647214894800 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (5356249 / 6578426281167140400 : ℚ) * p1 ^ 4 * p2
    + C (4670573 / 48441138979503488400 : ℚ) * p1 ^ 6

theorem moment6_0_eq : moment 6 0 = expanded6_0 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_0, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
