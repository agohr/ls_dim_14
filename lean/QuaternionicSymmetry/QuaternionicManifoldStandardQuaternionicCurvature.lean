import QuaternionicSymmetry.QuaternionicManifoldProjectiveSmooth
import QuaternionicSymmetry.LocalConnectionCommutantCurvature

/-! The actual local standard connection and curvature preserve the second
quaternionic generator as well as the chosen complex structure. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardQuaternionicCurvature
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardHilbertStructure
  QuaternionicManifoldProjectiveStandardConnection QuaternionicManifoldProjectiveSmooth
  ManifoldQuaternionicConnectionSplitting
  VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped ContDiff Manifold Topology Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (E →L[ℝ] (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E))) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

set_option maxHeartbeats 800000 in
theorem standardConnection_commutes_J (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (z : StandardSpace (E := E)) :
    standardConnection S Q D p y u ((standardStructure S).J z) =
      (standardStructure S).J (standardConnection S Q D p y u z) := by
  rw [standardConnection_apply]
  apply chartLie_commutes_J S Q p (D.form p y u)
  intro v
  have hc := symplecticConnection_commutes Q D p y u hy
    (Pi.basisFun ℝ (Fin 3) 1)
  have hv := congrArg (fun F : E →L[ℝ] E => F v) hc
  simpa only [symplecticConnection_apply,
    ManifoldQuaternionicRankThreeOrthogonal.synth_basis,
    quaternionicGenerator] using hv

set_option maxHeartbeats 800000 in
theorem standardCurvature_commutes_J (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (z : StandardSpace (E := E)) :
    LocalConnection.curvature (standardConnection S Q D p) y u v ((standardStructure S).J z) =
      (standardStructure S).J
        (LocalConnection.curvature (standardConnection S Q D p) y u v z) := by
  let T := (standardStructure S).J.toContinuousLinearEquiv.toContinuousLinearMap
  have hd : DifferentiableAt ℝ (standardConnection S Q D p) y :=
    ((standardConnection_smooth S Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  have hc := LocalConnectionCommutantCurvature.curvature_commutes
    (standardConnection S Q D p) T y u v hd (by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy] with x hx w
      apply ContinuousLinearMap.ext
      intro t
      exact standardConnection_commutes_J S Q D p x w hx t)
  exact congrArg (fun A : StandardSpace (E := E) →L[ℝ] StandardSpace (E := E) => A z) hc

end
end QuaternionicSymmetry.QuaternionicManifoldStandardQuaternionicCurvature
