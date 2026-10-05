import QuaternionicSymmetry.ManifoldQuaternionicIsometrySphereDerivative

/-! Horizontal covariance for the actual derivative-induced sphere action,
expressed in the genuine sphere tangent and induced connection coordinates. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryHorizontalAction

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometrySphereDerivative
open ManifoldQuaternionicIsometryInducedConnection
open ManifoldQuaternionicLocalSphereActionSmooth
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

/-- The actual target sphere point has the derivative-conjugated quaternionic
coefficient vector. -/
theorem localSphereAction_center_coefficients
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere) :
    sphereCoefficients (localSphereAction Q f p (p,u)) =
      coefficientOrbit Q f p (sphereCoefficients u)
        (extChartAt 𝓘(ℝ,E) p p) := by
  have h := localSphereAmbient_eq_coefficientField_on_overlap Q f p (p,u)
    (mem_chart_source E p) (mem_chart_source E (f • p))
  change EuclideanSpace.equiv (Fin 3) ℝ
      (localSphereAmbient Q f p (p,u)) = _
  rw [h]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply _

/-- A genuinely horizontal source-sphere tangent has a genuinely
horizontal target-sphere derivative. The target connection term is the
induced rank-three Levi-Civita form, not a stipulated weight. -/
theorem localSphereAction_horizontal_mfderiv_center
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere)
    (v : E) (w : TangentSpace (𝓡 2) u)
    (hw : EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap u w) =
      -(ManifoldQuaternionicAdjointConnection.inducedForm Q D p
        (extChartAt 𝓘(ℝ,E) p p) v (sphereCoefficients u))) :
    EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (localSphereAction Q f p (p,u))
        (mfderiv (J (E := E)) (𝓡 2)
          (localSphereAction Q f p) (p,u) (v,w))) =
      -(ManifoldQuaternionicAdjointConnection.inducedForm Q D (f • p)
        (ManifoldQuaternionicConnectionIsometrySolder.localIsometryChartMap
          Q f p (extChartAt 𝓘(ℝ,E) p p))
        (fderiv ℝ (ManifoldQuaternionicConnectionIsometrySolder.localIsometryChartMap
          Q f p) (extChartAt 𝓘(ℝ,E) p p) v)
        (sphereCoefficients (localSphereAction Q f p (p,u)))) := by
  rw [localSphereAction_mfderiv_coefficients_center Q f p u v w, hw,
    localSphereAction_center_coefficients Q f p u]
  simpa only [add_comm] using
    horizontal_coefficient_graph_covariant_center Q D f p v
      (sphereCoefficients u)

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryHorizontalAction
