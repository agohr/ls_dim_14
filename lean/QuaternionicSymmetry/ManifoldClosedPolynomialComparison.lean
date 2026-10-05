import QuaternionicSymmetry.ManifoldEvenClosedClassMap
import QuaternionicSymmetry.ManifoldEvenClosedEvaluation
import QuaternionicSymmetry.ManifoldSevenVariableClosedEvaluation
import QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation

/-! Polynomial expressions in actual closed forms commute both with taking
de Rham classes and with pointwise exterior evaluation. -/
namespace QuaternionicSymmetry.ManifoldClosedPolynomialComparison
open ManifoldEvenClosedClassMap
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (g : ManifoldSevenVariableClosedEvaluation.Generators (E := E) (M := M))

def classGenerators : ManifoldSevenVariableGradedEvaluation.Generators (E := E) (M := M) where
  u := classGrade 1 g.u
  p1 := classGrade 1 g.p1
  p2 := classGrade 2 g.p2
  p3 := classGrade 3 g.p3
  p4 := classGrade 4 g.p4
  p5 := classGrade 5 g.p5
  p6 := classGrade 6 g.p6

theorem class_evaluate (P : DimensionThirteenFourteenDensity.P) :
    classMap (ManifoldSevenVariableClosedEvaluation.evaluate g P) =
      ManifoldSevenVariableGradedEvaluation.evaluate (classGenerators g) P := by
  have hc : (classMap (E := E) (M := M)).comp ManifoldEvenClosedAlgebra.rationalConstants =
      ManifoldEvenCharacteristicAlgebra.rationalConstants := by
    exact Subsingleton.elim _ _
  have hg : (fun i => classMap (ManifoldSevenVariableClosedEvaluation.generatorValues g i)) =
      ManifoldSevenVariableGradedEvaluation.generatorValues (classGenerators g) := by
    funext i
    fin_cases i <;> exact classMap_of _ _
  change classMap (MvPolynomial.eval₂Hom _ _ P) = _
  rw [MvPolynomial.map_eval₂Hom, hc, hg]
  rfl

variable [FiniteDimensional ℝ E] (p : M) (y : E) (L : E →L[ℝ] E)

def fiberValues : Fin 7 → ManifoldEvenClosedEvaluation.FiberAlgebra (E := E) :=
  fun i => ManifoldEvenClosedEvaluation.evaluate p y L
    (ManifoldSevenVariableClosedEvaluation.generatorValues g i)

theorem pointwise_evaluate (P : DimensionThirteenFourteenDensity.P) :
    ManifoldEvenClosedEvaluation.evaluate p y L
      (ManifoldSevenVariableClosedEvaluation.evaluate g P) =
    MvPolynomial.aeval (fiberValues g p y L) P := by
  have hc : (ManifoldEvenClosedEvaluation.evaluate p y L).comp
      ManifoldEvenClosedAlgebra.rationalConstants =
      algebraMap ℚ (ManifoldEvenClosedEvaluation.FiberAlgebra (E := E)) := by
    exact Subsingleton.elim _ _
  change ManifoldEvenClosedEvaluation.evaluate p y L (MvPolynomial.eval₂Hom _ _ P) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  rfl

end
end QuaternionicSymmetry.ManifoldClosedPolynomialComparison
