import QuaternionicSymmetry.ManifoldClosedPolynomialRepresentative
import QuaternionicSymmetry.SixSevenPolynomialEvaluation
import QuaternionicSymmetry.QuaternionicTracePositivity

/-! The complexified exterior evaluation of a closed six-variable density
is precisely substitution of its six pointwise generator values. -/
namespace QuaternionicSymmetry.ManifoldClosedSixPolynomialEvaluation
open ManifoldClosedPolynomialRepresentative ManifoldClosedPolynomialComparison
open QuaternionicTracePositivity
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem pointwise_lift_representative
    (g : ManifoldSevenVariableClosedEvaluation.Generators (E := E) (M := M))
    {n : ℕ} (P : DimensionElevenTwelveDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift P) n)
    (p : M) (y : E) (L : E →L[ℝ] E) :
    embed (V := E) (ManifoldEvenClosedEvaluation.gradeValue p y L n
      (closedRepresentative g (DimensionThirteenFourteenDensity.lift P) hP)) =
    MvPolynomial.aeval (fun i : Fin 6 => embed (V := E) (fiberValues g p y L i.castSucc)) P := by
  rw [pointwise_representative]
  change ((embed (V := E)).restrictScalars ℚ) (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.comp_aeval_apply, SixSevenPolynomialEvaluation.aeval_lift]
  rfl

end
end QuaternionicSymmetry.ManifoldClosedSixPolynomialEvaluation
