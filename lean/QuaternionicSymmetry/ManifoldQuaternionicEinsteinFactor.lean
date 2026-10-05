import QuaternionicSymmetry.ManifoldQuaternionicSchurRicciDerivative

/-! A chart scalar Einstein factor extracted from one fixed nonzero vector.
It is defined from the actual Ricci and metric tensors. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateEinstein
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicCoordinateRicciDerivative
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
open QuaternionicSymmetry.LocalConnectionCurvatureSmooth
open QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAddCommGroup
    (LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ
    (LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedSpace
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def einsteinFactor (p : M) (c y : E) : ℝ :=
  coordinateRicci Q D p y c c / coordinateMetric Q p y c c

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateMetric_self_pos (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (c : E) (hc : c ≠ 0) : 0 < coordinateMetric Q p y c c := by
  rw [coordinateMetric]
  apply real_inner_self_pos.mpr
  intro hs
  apply hc
  apply (solderEquiv Q p y hy).injective
  simpa only [solderEquiv, map_zero] using hs

theorem einsteinFactor_eq_scalarRatio
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (c : E) (hc : c ≠ 0) :
    einsteinFactor Q D p c y =
      scalarRatio S Q D p y hy * ((Module.finrank ℝ E : ℝ) + 8) := by
  rw [einsteinFactor,
    coordinateRicci_einstein Q D S hdecomp p y hy c c]
  exact mul_div_cancel_right₀ _ (ne_of_gt (coordinateMetric_self_pos Q p y hy c hc))

omit [Nontrivial E] in
theorem einsteinFactor_differentiableAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (c : E) (hc : c ≠ 0) :
    DifferentiableAt ℝ (einsteinFactor Q D p c) y := by
  have hΓ := ManifoldQuaternionicCoordinateSecondBianchi.coordinateConnection_contDiffAt
    Q D p y hy
  have hR : DifferentiableAt ℝ (fun z => coordinateRicci Q D p z c c) y := by
    simp_rw [coordinateRicci_eq_ricciTrace Q D p]
    let L : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E) →L[ℝ] ℝ :=
      (realTraceCLM (V := E)).comp (ricciExtraction c c)
    change DifferentiableAt ℝ (fun z => L (LocalConnection.curvature
      (coordinateConnection Q D p) z)) y
    exact L.differentiableAt.comp y
      (curvature_differentiableAt (coordinateConnection Q D p) y hΓ)
  have hg : DifferentiableAt ℝ (fun z => coordinateMetric Q p z c c) y := by
    have hM := coordinateMetricField_differentiableAt Q p y hy
    have hM' := (hM.clm_apply (differentiableAt_const c)).clm_apply
      (differentiableAt_const c)
    exact (Filter.EventuallyEq.differentiableAt_iff
      (show (fun z => coordinateMetricField Q p z c c) =ᶠ[𝓝 y]
        (fun z => coordinateMetric Q p z c c) from by
          filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
            with z hz
          exact coordinateMetricField_apply Q p z hz c c)).mp hM'
  have hdiv := hR.mul (hg.inv
    (ne_of_gt (coordinateMetric_self_pos Q p y hy c hc)))
  simpa only [einsteinFactor, div_eq_mul_inv] using hdiv

end
end QuaternionicSymmetry.ManifoldQuaternionicEinsteinFactor
