import QuaternionicSymmetry.ManifoldQuaternionicEinsteinFactor

/-! Differentiation of the genuine local Einstein equation using the
compatible coordinate metric connection. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicEinsteinDerivative
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateEinstein
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetric_differentiableAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    DifferentiableAt ℝ (fun z => coordinateMetric Q p z v w) y := by
  have hM := coordinateMetricField_differentiableAt Q p y hy
  have hM' := (hM.clm_apply (differentiableAt_const v)).clm_apply
    (differentiableAt_const w)
  exact (Filter.EventuallyEq.differentiableAt_iff
    (show (fun z => coordinateMetricField Q p z v w) =ᶠ[𝓝 y]
      (fun z => coordinateMetric Q p z v w) from by
        filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
          with z hz
        exact coordinateMetricField_apply Q p z hz v w)).mp hM'

theorem coordinateRicci_einsteinFactor
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    coordinateRicci Q D p y v w =
      einsteinFactor Q D p c y * coordinateMetric Q p y v w := by
  rw [coordinateRicci_einstein Q D S hdecomp p y hy v w,
    einsteinFactor_eq_scalarRatio Q D S hdecomp p y hy c hc]

theorem coordinateRicci_covariant_einsteinFactor
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a v w : E) :
    fderiv ℝ (fun z => coordinateRicci Q D p z v w) y a -
      coordinateRicci Q D p y (coordinateConnection Q D p y a v) w -
        coordinateRicci Q D p y v (coordinateConnection Q D p y a w) =
      fderiv ℝ (einsteinFactor Q D p c) y a *
        coordinateMetric Q p y v w := by
  have heq : (fun z => coordinateRicci Q D p z v w) =ᶠ[𝓝 y]
      (fun z => einsteinFactor Q D p c z * coordinateMetric Q p z v w) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateRicci_einsteinFactor Q D S hdecomp p c hc z hz v w
  have hfactor := einsteinFactor_differentiableAt Q D p y hy c hc
  have hg := coordinateMetric_differentiableAt Q p y hy v w
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_mul hfactor hg] at hd
  have hdA := congrArg (fun L : E →L[ℝ] ℝ => L a) hd
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hdA
  have hm := coordinateConnection_metric Q D p y hy a v w
  rw [coordinateRicci_einsteinFactor Q D S hdecomp p c hc y hy
      (coordinateConnection Q D p y a v) w,
    coordinateRicci_einsteinFactor Q D S hdecomp p c hc y hy
      v (coordinateConnection Q D p y a w)]
  rw [hdA, hm]
  ring

end
end QuaternionicSymmetry.ManifoldQuaternionicEinsteinDerivative
