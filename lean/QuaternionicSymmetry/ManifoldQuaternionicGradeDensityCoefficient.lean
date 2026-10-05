import QuaternionicSymmetry.ManifoldQuaternionicFixedDensityCoefficient
import QuaternionicSymmetry.ManifoldEvenClosedEvaluation

/-! The coefficient in an evaluated actual closed top-degree grade is the
same intrinsic scalar density used by canonical manifold integration. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicGradeDensityCoefficient
open Module ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldEvenClosedAlgebra
open ManifoldEvenClosedEvaluation ManifoldFormExteriorEvaluation
open ManifoldQuaternionicFixedDensityCoefficient ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicVolumeCoefficient
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [Nontrivial E] [Nonempty M] in
theorem gradeValue_eq_value_cast (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (α : Grade E M (k + 1))
    (p : M) (y : E) (L : E →L[ℝ] E) :
    (gradeValue p y L (k + 1) α).val =
      value p y L (Module.finrank ℝ E)
        (castForm (show 4 * k + 3 + 1 = Module.finrank ℝ E by omega)
          α.val.val) := by
  change value p y L (4 * k + 3 + 1) α.val.val = _
  rw [value_cast]

theorem gradeValue_density_coefficient_iff
    (b : Basis ι ℝ E) (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (α : Grade E M (k + 1))
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (c : ℝ) :
    (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap (k + 1) α).val =
        c • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension ↔
      scalarDensity Q
        (castForm (show 4 * k + 3 + 1 = Module.finrank ℝ E by omega)
          α.val.val) ((extChartAt 𝓘(ℝ,E) p).symm y) = c := by
  rw [gradeValue_eq_value_cast k hdim α p y
    (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap]
  exact fixedDensity_coefficient_iff S Q b _ p y hy c

end
end QuaternionicSymmetry.ManifoldQuaternionicGradeDensityCoefficient
