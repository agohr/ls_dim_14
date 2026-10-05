import QuaternionicSymmetry.ManifoldQuaternionicConnectionUniqueness

/-! The actual curvature and scalar contractions are intrinsic to the
quaternionic Hermitian metric whenever a compatible torsion-free connection
exists: uniqueness on the chart open set also identifies its derivatives. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicLeviCivitaIntrinsic
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicConnectionUniqueness
open QuaternionicSymmetry.LocalConnection
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D₁ D₂ : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] in
theorem curvature_eq_on_chart (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    D₁.curvature Q p y = D₂.curvature Q p y := by
  have heq : D₁.form p =ᶠ[𝓝 y] D₂.form p := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact form_eq_on_chart Q D₁ D₂ p z hz
  have hderiv := heq.fderiv_eq (𝕜 := ℝ)
  have hval := form_eq_on_chart Q D₁ D₂ p y hy
  ext u v
  simp only [CompatibleTangentConnection.curvature, curvature_apply]
  rw [hval, hderiv]

theorem localScalarCurvature_eq_on_chart (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localScalarCurvature Q D₁ p y hy =
      localScalarCurvature Q D₂ p y hy := by
  have hcurv := curvature_eq_on_chart Q D₁ D₂ p y hy
  simp only [localScalarCurvature, localRicci, adaptedCurvature]
  rw [hcurv]

theorem preferredScalarCurvature_eq (x : M) :
    preferredScalarCurvature Q D₁ x =
      preferredScalarCurvature Q D₂ x :=
  localScalarCurvature_eq_on_chart Q D₁ D₂ x
    (extChartAt 𝓘(ℝ,E) x x)
    ((extChartAt 𝓘(ℝ,E) x).map_source (by simp))

end
end QuaternionicSymmetry.ManifoldQuaternionicLeviCivitaIntrinsic
