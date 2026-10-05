import QuaternionicSymmetry.ManifoldQuaternionicJointAdaptedDerivative
import QuaternionicSymmetry.ManifoldQuaternionicJointTangentAction

/-! Coordinate comparison for the spatial partial of BG-R3's smooth
evaluation without any common fixed-point condition. The source and target
charts are frozen at an arbitrary pair `(x₀, g₀ x₀)`. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointMovingDerivative

open Manifold
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ProdTangentCoordChange
open ManifoldQuaternionicJointAdaptedDerivative
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The spatial derivative of the smooth joint action, in frozen source
and target charts, is the derivative of the individual moving isometry. -/
theorem jointPartial_eq_individualMovingCharts
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (g₀ g : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ y : M)
    (hgg :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      g ∈ (chartAt V g₀).source)
    (hxy : y ∈ (chartAt E x₀).source)
    (hgy : g y ∈ (chartAt E (g₀ x₀)).source) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
      (fun p : (M ≃ᵢ M) × M => p.1 p.2)
      (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
      (g₀,x₀) (g,y)).comp (ContinuousLinearMap.inr ℝ V E) =
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E (g y)) (achart E (g₀ x₀)) (g y)).comp
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M) y).comp
          ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
            (achart E x₀) (achart E y) y)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  apply ContinuousLinearMap.ext
  intro v
  have hprod : (g,y) ∈ (chartAt (ModelProd V E) (g₀,x₀)).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source,
      Set.mem_prod] using And.intro hgg hxy
  rw [inTangentCoordinates_eq id
    (fun p : (M ≃ᵢ M) × M => p.1 p.2)
    (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      (fun p : (M ≃ᵢ M) × M => p.1 p.2)) hprod hgy]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    id_eq]
  rw [coordChange_prod_inr g₀ g x₀ y v hgg hxy]
  have hpart := actionPartial_eq_isometryDerivative Q hChart hManifold
    hAction g y
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E x₀) (achart E y) y v)
  exact congrArg
    (fun w : E => (tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E (g y)) (achart E (g₀ x₀)) (g y) w) hpart

end
end QuaternionicSymmetry.ManifoldQuaternionicJointMovingDerivative
