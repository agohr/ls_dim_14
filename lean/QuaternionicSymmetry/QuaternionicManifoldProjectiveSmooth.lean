import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointCore
import QuaternionicSymmetry.QuaternionicManifoldProjectiveStandardConnection

/-! Smoothness of the actual local standard connection and of the descended
projective adjoint transition maps. -/
namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveSmooth

open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardAdjoint
  QuaternionicManifoldProjectiveStandardConnection
  QuaternionicManifoldProjectiveAdjointCore QuaternionicManifoldProjectiveAdjointLocal
  QuaternionicManifoldStandardLocalOperator QuaternionicManifoldLocalScalarLifts
  ManifoldQuaternionicConnection
open scoped ContDiff Manifold Topology Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

-- Binding the existing normed structure once lets typeclass search infer
-- nested operator spaces over the Hilbert direct sum without instance diamonds.
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ (StandardEnd (E := E)) := inferInstance
local instance : NormedSpace ℝ (StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) := inferInstance

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem standardConnection_smooth (p : M) :
    ContDiffOn ℝ ∞ (standardConnection S Q D p) (extChartAt 𝓘(ℝ, E) p).target := by
  exact contDiffOn_const.clm_comp (D.smooth_form p)

private def realAdjointCLM : StandardEnd (E := E) →L[ℝ] StandardEnd (E := E) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearMap

private def leftCompositionCLM : StandardEnd (E := E) →L[ℝ]
    (StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) :=
  ContinuousLinearMap.compL ℝ (StandardSpace (E := E))
    (StandardSpace (E := E)) (StandardSpace (E := E))

private def rightCompositionCLM : StandardEnd (E := E) →L[ℝ]
    (StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) :=
  (ContinuousLinearMap.compL ℝ (StandardSpace (E := E))
    (StandardSpace (E := E)) (StandardSpace (E := E))).flip

set_option maxHeartbeats 800000 in
theorem localAdjointOperator_smooth (i j : atlas E M) (q : unitary ℍ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) ∞
      (localAdjointOperator S Q i j q) (liftNeighborhood Q i j q) := by
  have hG := smooth_localStandardOperator S Q i j q
  have hGstar : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, StandardEnd (E := E)) ∞
      (fun y : M => (localStandardOperator S Q i j q y).adjoint)
      (liftNeighborhood Q i j q) := by
    simpa only [Function.comp_def, realAdjointCLM] using
      ((realAdjointCLM (E := E)).contMDiff.comp_contMDiffOn hG)
  have hL : ContMDiff 𝓘(ℝ, StandardEnd (E := E))
      𝓘(ℝ, StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) ∞
      (leftCompositionCLM (E := E)) := ContinuousLinearMap.contMDiff _
  have hR : ContMDiff 𝓘(ℝ, StandardEnd (E := E))
      𝓘(ℝ, StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) ∞
      (rightCompositionCLM (E := E)) := ContinuousLinearMap.contMDiff _
  have hleft : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) ∞
      (fun y => (ContinuousLinearMap.compL ℝ (StandardSpace (E := E))
        (StandardSpace (E := E)) (StandardSpace (E := E))) (localStandardOperator S Q i j q y))
      (liftNeighborhood Q i j q) := by
    exact hL.comp_contMDiffOn hG
  have hright : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) ∞
      (fun y => ((ContinuousLinearMap.compL ℝ (StandardSpace (E := E))
        (StandardSpace (E := E)) (StandardSpace (E := E))).flip)
          ((localStandardOperator S Q i j q y).adjoint))
      (liftNeighborhood Q i j q) := by
    exact hR.comp_contMDiffOn hGstar
  exact hright.clm_comp hleft

theorem projectiveCoordChange_smooth (i j : atlas E M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) ∞
      (projectiveCoordChange S Q i j) (overlap Q i j) := by
  intro x hx
  obtain ⟨q, hqx, hopen, _, _⟩ := exists_local_scalar_lift Q S i j x hx.1 hx.2
  have hlocal := (localAdjointOperator_smooth S Q i j q).contMDiffAt (hopen.mem_nhds hqx)
  apply ContMDiffAt.contMDiffWithinAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hqx] with y hy
  exact projectiveCoordChange_eq_local S Q i j q y hy

instance projectiveCore_isContMDiff :
    (projectiveCore S Q).IsContMDiff 𝓘(ℝ, E) ∞ where
  contMDiffOn_coordChange i j := projectiveCoordChange_smooth S Q i j

theorem projectiveTotalSpace_isManifold :
    IsManifold ((𝓘(ℝ, E)).prod 𝓘(ℝ, StandardEnd (E := E))) ∞
      (projectiveCore S Q).TotalSpace := by
  infer_instance

end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveSmooth
