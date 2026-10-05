import QuaternionicSymmetry.ManifoldClosedPolynomialRepresentative
import QuaternionicSymmetry.ManifoldFormExteriorReflection

/-! The representative of a pure generator power is its actual normalized
wedge power, with all degree casts accounted for. -/
namespace QuaternionicSymmetry.ManifoldClosedGeneratorPower
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldFormPowers
open ManifoldFormExteriorEvaluation ManifoldFormExteriorReflection
open ManifoldSevenVariableClosedEvaluation ManifoldClosedPolynomialRepresentative
open ManifoldClosedPolynomialComparison ManifoldEvenClosedEvaluation
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (g : Generators (E := E) (M := M))

theorem representative_u_power (k : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous slotGrade
      (MvPolynomial.X (0 : Fin 7) ^ (k+1) : DimensionThirteenFourteenDensity.P) (k+1)) :
    (closedRepresentative g (MvPolynomial.X (0 : Fin 7) ^ (k+1)) hP).val.val =
      castForm (show 4*(k+1) = 4*k+3+1 by omega) (formPower g.u.val.val (k+1)) := by
  funext x
  have hv := pointwise_representative g
    (MvPolynomial.X (0 : Fin 7) ^ (k+1)) hP x (extChartAt 𝓘(ℝ,E) x x)
      (ContinuousLinearMap.id ℝ E)
  rw [map_pow, MvPolynomial.aeval_X] at hv
  have hzero : fiberValues g x (extChartAt 𝓘(ℝ,E) x x) (ContinuousLinearMap.id ℝ E) 0 =
      gradeValue x (extChartAt 𝓘(ℝ,E) x x) (ContinuousLinearMap.id ℝ E) 1 g.u := by
    exact evaluate_of _ _ _ _ _
  rw [hzero] at hv
  have hv' := congrArg Subtype.val hv
  change value x (extChartAt 𝓘(ℝ,E) x x) (ContinuousLinearMap.id ℝ E) _
    (closedRepresentative g (MvPolynomial.X (0 : Fin 7) ^ (k+1)) hP).val.val =
      (value x (extChartAt 𝓘(ℝ,E) x x) (ContinuousLinearMap.id ℝ E) 4 g.u.val.val)^(k+1) at hv'
  have he := tangent_eq_of_value_eq x (ContinuousLinearEquiv.refl ℝ E)
    (closedRepresentative g (MvPolynomial.X (0 : Fin 7) ^ (k+1)) hP).val.val
    (castForm (show 4*(k+1) = 4*k+3+1 by omega) (formPower g.u.val.val (k+1))) 1
    (by simpa only [one_smul, value_cast, value_formPower] using hv')
  simpa only [one_smul] using he

end
end QuaternionicSymmetry.ManifoldClosedGeneratorPower
