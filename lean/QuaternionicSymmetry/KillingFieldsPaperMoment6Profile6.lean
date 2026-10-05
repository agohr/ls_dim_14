import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile5
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def expanded6_6 : P :=
  C (123896848241 / 3471235781010747750 : ℚ) * p6
    + C (41658002629 / 2911821750186701625 : ℚ) * p1 * p5
    + C (-2386331443696649 / 40407983432069159907000 : ℚ) * p2 * p4
    + C (-16153202951674249 / 40407983432069159907000 : ℚ) * p1 ^ 2 * p4
    + C (-15743555051161523 / 3286034938386481325294250 : ℚ) * p3 ^ 2
    + C (-6417028942062019 / 64432057615421202456750 : ℚ) * p1 * p2 * p3
    + C (-140871990615418903 / 657206987677296265058850 : ℚ) * p1 ^ 3 * p3
    + C (137774137664511541 / 4089287923325398982588400 : ℚ) * p2 ^ 3
    + C (3159773246395339039 / 4089287923325398982588400 : ℚ) * p1 ^ 2 * p2 ^ 2
    + C (124978306595893441051 / 61339318849880984738826000 : ℚ) * p1 ^ 4 * p2
    + C (202184782847008477727 / 184017956549642954216478000 : ℚ) * p1 ^ 6

theorem moment6_6_eq : moment 6 6 = expanded6_6 := by
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, moment, profile, expanded6_6, H2WitnessThirteen.embed,
    FiniteTypeCSchurSix.orbital, FiniteTypeCSchurSix.partitions, FiniteTypeCSchurSix.schurValue, FiniteTypeCSchurSix.schur, FiniteTypeCSchurSix.powerSum, QuarticOrbitalEleven.factorialRho, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5, FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5, FiniteTypeCSchurSix.p6, Nat.factorial, u, p1, p2, p3, p4, p5, p6]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring


end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
