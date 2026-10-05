import QuaternionicSymmetry.ManifoldEvenClosedEvaluation
import QuaternionicSymmetry.ManifoldFormExteriorReflection

/-! Equality of positive closed grades can be proved in pointwise exterior
algebras at chart centers, using any family of invertible tangent frames. -/
namespace QuaternionicSymmetry.ManifoldClosedGradeReflection
open ManifoldEvenClosedAlgebra ManifoldEvenClosedEvaluation
open ManifoldFormExteriorEvaluation ManifoldFormExteriorReflection
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem eq_of_center_values (k : ℕ) (α β : Grade E M (k+1))
    (L : M → E ≃L[ℝ] E)
    (h : ∀ x : M, gradeValue x (extChartAt 𝓘(ℝ,E) x x)
      (L x).toContinuousLinearMap (k+1) α =
        gradeValue x (extChartAt 𝓘(ℝ,E) x x) (L x).toContinuousLinearMap (k+1) β) :
    α = β := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hv := congrArg Subtype.val (h x)
  have he := tangent_eq_of_value_eq x (L x) α.val.val β.val.val 1
    (by simpa only [one_smul] using hv)
  simpa only [one_smul] using he

end
end QuaternionicSymmetry.ManifoldClosedGradeReflection
