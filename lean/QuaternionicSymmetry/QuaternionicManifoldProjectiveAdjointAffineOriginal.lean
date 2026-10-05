import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointOriginalGauge

/-! Affine descent of the induced connection on the actual original
projective adjoint bundle, using the projective cocycle as gauge. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointAffineOriginal

open scoped Manifold ContDiff Quaternion Topology
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicManifoldProjectiveAdjointCore
open QuaternionicManifoldProjectiveAdjointOriginalGauge
open QuaternionicManifoldProjectiveAdjointAffineRefined
open QuaternionicManifoldProjectiveAdjointConnection
open QuaternionicProjectiveAdjointGaugeDerivative
open ManifoldQuaternionicConnection
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardL2.StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E) →L[ℝ]
      QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) := inferInstance

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def projectiveChart (p q : M) (y : E) :=
  projectiveCoordChange S Q (achart E p) (achart E q)
    ((extChartAt 𝓘(ℝ, E) p).symm y)

def projectiveChartInverse (p q : M) (y : E) :=
  projectiveCoordChange S Q (achart E q) (achart E p)
    ((extChartAt 𝓘(ℝ, E) p).symm y)

set_option maxHeartbeats 800000 in
theorem adjointConnection_affine_original (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    adjointConnection S Q D p y =
      LocalConnectionGauge.transform
        (LocalConnectionCoordinatePullback.pullback
          (adjointConnection S Q D q)
          (chartTransition (I := 𝓘(ℝ, E)) p q))
        (projectiveChart S Q p q) (projectiveChartInverse S Q p q) y := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using
      (extChartAt 𝓘(ℝ, E) p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using hy.2
  obtain ⟨lift, hx, hopen, _, _⟩ :=
    exists_local_scalar_lift Q S (achart E p) (achart E q) x hp hq
  let G := standardChart S Q p (achart E p) (achart E q) lift
  let K := standardChartInverse S Q p (achart E p) (achart E q) lift
  have hneigh : ∀ᶠ z in 𝓝 y,
      (extChartAt 𝓘(ℝ, E) p).symm z ∈
        liftNeighborhood Q (achart E p) (achart E q) lift :=
    (continuousAt_extChartAt_symm'' hy.1).preimage_mem_nhds
      (hopen.mem_nhds hx)
  have hF : projectiveChart S Q p q =ᶠ[𝓝 y] conjugationGauge G K := by
    filter_upwards [hneigh] with z hz
    exact projectiveChart_eq_conjugation S Q p q lift z hz
  have hH : projectiveChartInverse S Q p q =ᶠ[𝓝 y]
      conjugationGauge K G := by
    filter_upwards [hneigh] with z hz
    exact projectiveChartReverse_eq_conjugation S Q p q lift z hz
  have hRef := adjointConnection_affine_refined S Q D p q lift y hy hx
  apply ContinuousLinearMap.ext
  intro u
  change adjointConnection S Q D p y u = _
  rw [hRef]
  simp only [LocalConnectionGauge.transform_apply, hF.self_of_nhds,
    hH.self_of_nhds, hF.fderiv_eq]
  rfl

end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointAffineOriginal
