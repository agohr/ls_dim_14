import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile2
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_3 : P :=
  C (310176397 / 156205610145483648750 : ℚ) * p6
    + C (-451147189 / 32030039252053717875 : ℚ) * p1 * p5
    + C (-6325836951671 / 929383618937590677861000 : ℚ) * p2 * p4
    + C (-31062653857999 / 929383618937590677861000 : ℚ) * p1 ^ 2 * p4
    + C (-2457811903823 / 16430174691932406626471250 : ℚ) * p3 ^ 2
    + C (73244728571893 / 5476724897310802208823750 : ℚ) * p1 * p2 * p3
    + C (354137430697357 / 16430174691932406626471250 : ℚ) * p1 ^ 3 * p3
    + C (25048803652883 / 4444878177527607589770000 : ℚ) * p2 ^ 3
    + C (9177474857713847 / 102232198083134974564710000 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (3000929459135999 / 18040976132317936687890000 : ℚ) * p1 ^ 4 * p2
    + C (58543435932773723 / 920089782748214771082390000 : ℚ) * p1 ^ 6

theorem moment6_3_eq : moment 6 3 = expanded6_3 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_3, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
