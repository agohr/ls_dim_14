import QuaternionicSymmetry.GeneralLeviCivitaCoordinateUniqueness

/-! The ordinary coordinate Levi-Civita form is determined pointwise by
the first derivatives of the chart metric. This is derived from its
metric and torsion laws, not added as a model-specific premise. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaCoordinateKoszul

open Manifold Bundle GeneralLeviCivitaSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem coordinate_koszul
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (D : CoordinateLeviCivitaConnection g)
    (p : M) (y u v w : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    2 * chartMetric g p y (D.form p y u v) w =
      fderiv ℝ (fun z => chartMetric g p z v w) y u +
      fderiv ℝ (fun z => chartMetric g p z u w) y v -
      fderiv ℝ (fun z => chartMetric g p z u v) y w := by
  have h₁ := D.metric p y u v w hy
  have h₂ := D.metric p y v u w hy
  have h₃ := D.metric p y w u v hy
  rw [D.torsion p y v u hy] at h₂
  rw [D.torsion p y w u hy, D.torsion p y w v hy] at h₃
  have hsym (a b : E) : chartMetric g p y a b = chartMetric g p y b a := by
    exact g.symm _ _ _
  rw [hsym v (D.form p y u w)] at h₁
  linarith only [h₁, h₂, h₃]

end
end QuaternionicSymmetry.GeneralLeviCivitaCoordinateKoszul
