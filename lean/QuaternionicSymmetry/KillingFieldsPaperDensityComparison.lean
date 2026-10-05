import QuaternionicSymmetry.KillingFieldsPaperDensity
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

theorem density2_eq_existing : density 2 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 2) := by
  simp only [FiniteVirtualDensity.density]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced2, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₂, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density3_eq_existing : density 3 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 3) := by
  simp only [FiniteVirtualDensity.density]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced3, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₃, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density4_eq_existing : density 4 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 4) := by
  simp only [FiniteVirtualDensity.density]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced4, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₄, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density5_eq_existing : density 5 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 5) := by
  simp only [FiniteVirtualDensity.density]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced5, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₅, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density6_eq_existing : density 6 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 6) := by
  simp only [FiniteVirtualDensity.density]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced6, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₆, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density7_eq_existing : density 7 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 7) := by
  simp only [FiniteVirtualDensity.density]
  rw [← PrintedCertificatesSevenTen.certificate7]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced7, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₇, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density8_eq_existing : density 8 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 8) := by
  simp only [FiniteVirtualDensity.density]
  rw [← PrintedCertificatesSevenTen.certificate8]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced8, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₈, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density9_eq_existing : density 9 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 9) := by
  simp only [FiniteVirtualDensity.density]
  rw [← PrintedCertificatesSevenTen.certificate9]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced9, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₉, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density10_eq_existing : density 10 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 10) := by
  simp only [FiniteVirtualDensity.density]
  rw [← PrintedCertificatesSevenTen.certificate10]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced10, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, AlgebraCertificates.K₁₀, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density11_eq_existing : density 11 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 11) := by
  simp only [FiniteVirtualDensity.density]
  rw [DimensionElevenTwelveDensity.density11_printed]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced11, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, DimensionElevenTwelveDensity.printed11, DimensionElevenTwelveDensity.q11, DimensionElevenTwelveDensity.f5, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem density12_eq_existing : density 12 =
    DimensionThirteenFourteenDensity.lift (FiniteVirtualDensity.density 12) := by
  simp only [FiniteVirtualDensity.density]
  rw [DimensionElevenTwelveDensity.density12_printed]
  apply MvPolynomial.funext
  intro v
  norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat, Matrix.cons_val, MvPolynomial.bind₁_C_right, density, reduced, reduced12, DimensionThirteenFourteenDensity.lift, PrintedTwoSixLinearAssembly.density2, PrintedTwoSixLinearAssembly.density3, PrintedTwoSixLinearAssembly.density4, ReconstructionExamples.k5, ReconstructionExamples.k6, DimensionElevenTwelveDensity.old, AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄, AlgebraCertificates.A₀, AlgebraCertificates.A₁, AlgebraCertificates.A₂, AlgebraCertificates.A₃, AlgebraCertificates.A₄, AlgebraCertificates.b₁, AlgebraCertificates.b₂, AlgebraCertificates.b₃, AlgebraCertificates.b₄, DimensionElevenTwelveDensity.printed12, DimensionElevenTwelveDensity.q12, DimensionElevenTwelveDensity.f5, u, p1, p2, p3, p4, p5, p6, DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5]
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
