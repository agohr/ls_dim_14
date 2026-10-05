import QuaternionicSymmetry.ManifoldClosedPolynomialComparison

/-! A weighted characteristic polynomial has a genuine global closed
representative, with exact pointwise and de Rham evaluation formulas. -/
namespace QuaternionicSymmetry.ManifoldClosedPolynomialRepresentative
open ManifoldSevenVariableClosedEvaluation ManifoldClosedPolynomialComparison
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (g : Generators (E := E) (M := M))
  {n : ℕ} (P : DimensionThirteenFourteenDensity.P)
  (hP : MvPolynomial.IsWeightedHomogeneous slotGrade P n)

def closedRepresentative : ManifoldEvenClosedAlgebra.Grade E M n :=
  (pureGrade_of_weighted g hP).choose

theorem evaluate_eq_of :
    evaluate g P = DirectSum.of (ManifoldEvenClosedAlgebra.Grade E M) n
      (closedRepresentative g P hP) :=
  (pureGrade_of_weighted g hP).choose_spec

theorem class_evaluate_eq_of :
    ManifoldSevenVariableGradedEvaluation.evaluate (classGenerators g) P =
      DirectSum.of (ManifoldEvenCharacteristicAlgebra.Grade E M) n
        (ManifoldEvenClosedClassMap.classGrade n (closedRepresentative g P hP)) := by
  rw [← class_evaluate, evaluate_eq_of g P hP, ManifoldEvenClosedClassMap.classMap_of]

variable [FiniteDimensional ℝ E]

theorem pointwise_representative (p : M) (y : E) (L : E →L[ℝ] E) :
    ManifoldEvenClosedEvaluation.gradeValue p y L n (closedRepresentative g P hP) =
      MvPolynomial.aeval (fiberValues g p y L) P := by
  rw [← pointwise_evaluate, evaluate_eq_of g P hP, ManifoldEvenClosedEvaluation.evaluate_of]

end
end QuaternionicSymmetry.ManifoldClosedPolynomialRepresentative
