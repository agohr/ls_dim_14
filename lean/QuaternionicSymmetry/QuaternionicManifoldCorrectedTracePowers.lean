import QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
import QuaternionicSymmetry.QuaternionicManifoldStandardChartDifferentiability
import QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
import QuaternionicSymmetry.LocalChernWeilSmoothness

/-! Every positive standard trace power of the actual solder-corrected
connection is a global closed form. Smooth lifts are chosen only near the
point where the scalar form transition law is proved. -/
namespace QuaternionicSymmetry.QuaternionicManifoldCorrectedTracePowers
open QuaternionicManifoldCorrectedConnection QuaternionicProjectiveStandardL2
open QuaternionicManifoldStandardMaurerIdentity QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldStandardChartDifferentiability
open QuaternionicManifoldProductRepresentationPointwise
open QuaternionicManifoldStandardLocalOperator ManifoldQuaternionicConnection
open ManifoldChernWeilGluing ManifoldDifferentialForms
open LocalChernWeilTracePowers LocalConnectionCoordinatePullback
open scoped Manifold ContDiff Quaternion Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem standardChart_contDiffAt (p : M) (i j : atlas E M) (lift : unitary ℍ)
    (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hx : (extChartAt 𝓘(ℝ,E) p).symm y ∈ liftNeighborhood Q i j lift) :
    ContDiffAt ℝ ∞ (standardChart S Q p i j lift) y := by
  have hG := (smooth_localStandardOperator S Q i j lift).contMDiffAt
    ((isOpen_liftNeighborhood Q i j lift).mem_nhds hx)
  have hC := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  exact (hG.comp y hC).contDiffAt

set_option maxHeartbeats 800000 in
theorem trace_coordinate (t : ℝ) (k : ℕ) (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    traceCurvaturePowerForm (correctedConnection S Q D t p) k y =
      (traceCurvaturePowerForm (correctedConnection S Q D t q) k
        (chartTransition (I := 𝓘(ℝ,E)) p q y)).compContinuousLinearMap
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy.2
  obtain ⟨lift, hx, hopen, _, _⟩ :=
    exists_local_scalar_lift Q S (achart E p) (achart E q) x hp hq
  let G := standardChart S Q p (achart E p) (achart E q) lift
  let K := standardChartInverse S Q p (achart E p) (achart E q) lift
  let φ := chartTransition (I := 𝓘(ℝ,E)) p q
  have hneigh : ∀ᶠ z in 𝓝 y, (extChartAt 𝓘(ℝ,E) p).symm z ∈
      liftNeighborhood Q (achart E p) (achart E q) lift :=
    (continuousAt_extChartAt_symm'' hy.1).preimage_mem_nhds (hopen.mem_nhds hx)
  have hAffine : correctedConnection S Q D t p =ᶠ[𝓝 y]
      LocalConnectionGauge.transform (pullback (correctedConnection S Q D t q) φ) G K := by
    filter_upwards [hneigh, (chartOverlap_isOpen (I := 𝓘(ℝ,E)) p q).mem_nhds hy]
      with z hz hz'
    exact correctedConnection_affine_refined S Q D t p q lift z hz' hz
  have hleft : (fun z => K z * G z) =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [hneigh] with z hz
    exact standardChartInverse_mul_standardChart S Q p q lift z hz
  have hright : G y * K y = 1 := by
    dsimp only [G, K]
    rw [standardChart_eq_localProductLift S Q p q lift y hx,
      standardChartInverse_eq_localProductLift S Q p q lift y hx]
    apply ContinuousLinearMap.ext
    intro z
    exact (standardActionL2 S _).apply_symm_apply z
  have hφ : ContDiffAt ℝ 2 φ y := by
    simpa [φ, chartTransition] using
      (contDiffWithinAt_ext_coord_change (I := 𝓘(ℝ,E)) (n := 2) q p hy)
  have hΓq : DifferentiableAt ℝ (correctedConnection S Q D t q) (φ y) :=
    ((correctedConnection_smooth S Q D t q).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) q).mem_nhds
        ((extChartAt 𝓘(ℝ,E) q).map_source hy.2))
  exact tracePowerForm_gauge_coordinate LocalEndomorphismTrace.traceCLM
    LocalEndomorphismTrace.traceCLM_cyclic
    (correctedConnection S Q D t p) (correctedConnection S Q D t q) φ G K y
    hAffine hΓq hφ
    ((standardChart_contDiffAt S Q p _ _ lift y hy.1 hx).of_le ENat.LEInfty.out)
    (standardChartInverse_differentiableAt S Q p q lift y hy.1 hx)
    hleft hright k

def traceAtlas (t : ℝ) (k : ℕ) :
    TracePowerAtlas (E := E) (M := M) (V := StandardSpace (E := E)) k where
  connection := correctedConnection S Q D t
  connectionC2 p _ hy := ((correctedConnection_smooth S Q D t p).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)).of_le ENat.LEInfty.out
  traceRegular p := LocalChernWeilSmoothness.tracePowerForm_contDiffOn
    LocalEndomorphismTrace.traceCLM _ (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p)
    (correctedConnection_smooth S Q D t p) k
  traceCoordinateLaw p q y hp hq := trace_coordinate S Q D t k p q y ⟨hp, hq⟩

def closedTracePower (t : ℝ) (k : ℕ) :
    closedForms (E := E) (M₀ := M) (powerDegree k) :=
  (traceAtlas S Q D t k).closedGlobalForm

end
end QuaternionicSymmetry.QuaternionicManifoldCorrectedTracePowers
