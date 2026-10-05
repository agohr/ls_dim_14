import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointAffineOriginal
import QuaternionicSymmetry.QuaternionicManifoldAdjointConnectionSmooth
import QuaternionicSymmetry.QuaternionicManifoldProjectiveSmooth
import QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
import QuaternionicSymmetry.LocalChernWeilSmoothness

/-! Global trace powers of the genuine projective standard adjoint connection. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointChernWeil

open scoped Manifold ContDiff Quaternion Topology
open QuaternionicManifoldProjectiveAdjointAffineOriginal
open QuaternionicManifoldProjectiveAdjointCore
open QuaternionicManifoldProjectiveSmooth
open QuaternionicManifoldAdjointConnectionSmooth
open QuaternionicManifoldProjectiveAdjointConnection
open ManifoldChernWeilGaugeDescent
open ManifoldChernWeilGluing
open ManifoldDifferentialForms
open LocalChernWeilSmoothness
open ManifoldQuaternionicConnection
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardL2.StandardSpace (E := E)) := inferInstance
local instance : NormedAddCommGroup (QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) := inferInstance
local instance : NormedAddCommGroup
    (QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E) →L[ℝ]
      QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E) →L[ℝ]
      QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) := inferInstance

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private theorem projectiveChart_contDiffAt (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    ContDiffAt ℝ 2 (projectiveChart S Q p q) y := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using
      (extChartAt 𝓘(ℝ, E) p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using hy.2
  have hopen : IsOpen (QuaternionicManifoldLocalScalarLifts.overlap Q (achart E p) (achart E q)) :=
    (Q.frames.adaptedCore.isOpen_baseSet _).inter (Q.frames.adaptedCore.isOpen_baseSet _)
  have hframe := ((projectiveCoordChange_smooth S Q (achart E p) (achart E q)).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).contMDiffAt
      (hopen.mem_nhds ⟨hp, hq⟩)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
      (extChartAt 𝓘(ℝ, E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy.1).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy.1)
  exact (hframe.comp y hsymm).contDiffAt

private theorem projectiveChartInverse_contDiffAt (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    ContDiffAt ℝ 2 (projectiveChartInverse S Q p q) y := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using
      (extChartAt 𝓘(ℝ, E) p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using hy.2
  have hopen : IsOpen (QuaternionicManifoldLocalScalarLifts.overlap Q (achart E q) (achart E p)) :=
    (Q.frames.adaptedCore.isOpen_baseSet _).inter (Q.frames.adaptedCore.isOpen_baseSet _)
  have hframe := ((projectiveCoordChange_smooth S Q (achart E q) (achart E p)).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).contMDiffAt
      (hopen.mem_nhds ⟨hq, hp⟩)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
      (extChartAt 𝓘(ℝ, E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy.1).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy.1)
  exact (hframe.comp y hsymm).contDiffAt

set_option maxHeartbeats 800000 in
def gaugeAtlas (k : ℕ) :
    GaugeCoordinateAtlas (E := E) (M := M)
      (V := QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) k where
  connection := adjointConnection S Q D
  connectionC2 p y hy :=
    ((adjointConnection_smooth S Q D p).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)).of_le
      (by exact ENat.LEInfty.out)
  traceRegular p :=
    tracePowerForm_contDiffOn
      QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
      (adjointConnection S Q D p)
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p)
      (adjointConnection_smooth S Q D p) k
  gauge := projectiveChart S Q
  inverseGauge := projectiveChartInverse S Q
  connectionGaugeLaw p q y hp hq := by
    have hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q := ⟨hp, hq⟩
    filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).mem_nhds hy]
      with z hz
    exact adjointConnection_affine_original S Q D p q z hz
  gaugeC2 p q y hp hq := projectiveChart_contDiffAt S Q p q y ⟨hp, hq⟩
  inverseGaugeDifferentiable p q y hp hq :=
    (projectiveChartInverse_contDiffAt S Q p q y ⟨hp, hq⟩).differentiableAt
      (by norm_num)
  inverseLeft p q y hp hq := by
    have hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q := ⟨hp, hq⟩
    filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).mem_nhds hy]
      with z hz
    let x := (extChartAt 𝓘(ℝ, E) p).symm z
    have hp' : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
      simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using
        (extChartAt 𝓘(ℝ, E) p).map_target hz.1
    have hq' : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
      simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using hz.2
    apply ContinuousLinearMap.ext
    intro B
    change projectiveCoordChange S Q (achart E q) (achart E p) x
      (projectiveCoordChange S Q (achart E p) (achart E q) x B) = B
    rw [projectiveCoordChange_comp S Q (achart E p) (achart E q)
      (achart E p) x hp' hq' hp', projectiveCoordChange_self S Q
        (achart E p) x hp']
  inverseRight p q y hp hq := by
    let x := (extChartAt 𝓘(ℝ, E) p).symm y
    have hp' : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
      simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using
        (extChartAt 𝓘(ℝ, E) p).map_target hp
    have hq' : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
      simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ, E)] using hq
    apply ContinuousLinearMap.ext
    intro B
    change projectiveCoordChange S Q (achart E p) (achart E q) x
      (projectiveCoordChange S Q (achart E q) (achart E p) x B) = B
    rw [projectiveCoordChange_comp S Q (achart E q) (achart E p)
      (achart E q) x hq' hp' hq', projectiveCoordChange_self S Q
        (achart E q) x hq']

/-- Every trace curvature power of the induced connection descends to a
closed global form on the original projective adjoint bundle. -/
def traceCurvaturePower (k : ℕ) :
    Form 𝓘(ℝ, E) M (LocalChernWeilTracePowers.powerDegree k) :=
  ((gaugeAtlas S Q D k).toTracePowerAtlas).globalForm

theorem traceCurvaturePower_closed
    (S : QuaternionicStructure E)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
    (D : CompatibleTangentConnection Q) (k : ℕ) :
    exteriorDerivative (traceCurvaturePower S Q D k) = 0 :=
  ((gaugeAtlas S Q D k).toTracePowerAtlas).globalForm_closed

end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointChernWeil
