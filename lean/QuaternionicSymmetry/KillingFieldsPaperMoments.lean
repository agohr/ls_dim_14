import QuaternionicSymmetry.KillingFieldsPaperMoment6Profile11
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def eta : P := C (192 : ℚ) * (u ^ 2 * moment 1 0 + moment 3 0)

def expandedEta : P :=
  C (960 / 203 : ℚ) * u ^ 2 * p1
    + C (20560 / 72891819 : ℚ) * p3
    + C (136 / 207669 : ℚ) * p1 * p2
    + C (27176 / 72891819 : ℚ) * p1 ^ 3

theorem eta_eq : eta = expandedEta := by
  rw [eta, moment1_0_eq, moment3_0_eq]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, expanded1_0, expanded3_0, expandedEta]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
