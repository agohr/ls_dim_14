import QuaternionicSymmetry.QuaternionicManifoldCorrectedTracePowers

/-! One smooth local gauge transports the whole corrected connection path
near any point of an original chart overlap. -/
namespace QuaternionicSymmetry.QuaternionicManifoldCorrectedGaugeGerm
open QuaternionicManifoldCorrectedConnection QuaternionicManifoldCorrectedTracePowers
open QuaternionicProjectiveStandardL2 QuaternionicManifoldStandardMaurerIdentity
open QuaternionicManifoldLocalScalarLifts QuaternionicManifoldStandardChartDifferentiability
open QuaternionicManifoldProductRepresentationPointwise ManifoldQuaternionicConnection
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
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem exists_gauge (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    ∃ G K : E → (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)),
      ContDiffAt ℝ 2 G y ∧ DifferentiableAt ℝ K y ∧
      ((fun z => K z * G z) =ᶠ[𝓝 y] fun _ => 1) ∧ G y * K y = 1 ∧
      ∀ t : ℝ, correctedConnection S Q D t p =ᶠ[𝓝 y]
        LocalConnectionGauge.transform
          (LocalConnectionCoordinatePullback.pullback (correctedConnection S Q D t q)
            (chartTransition (I := 𝓘(ℝ,E)) p q)) G K := by
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
  have hneigh : ∀ᶠ z in 𝓝 y, (extChartAt 𝓘(ℝ,E) p).symm z ∈
      liftNeighborhood Q (achart E p) (achart E q) lift :=
    (continuousAt_extChartAt_symm'' hy.1).preimage_mem_nhds (hopen.mem_nhds hx)
  refine ⟨G, K, (standardChart_contDiffAt S Q p _ _ lift y hy.1 hx).of_le
    ENat.LEInfty.out, standardChartInverse_differentiableAt S Q p q lift y hy.1 hx,
    ?_, ?_, ?_⟩
  · filter_upwards [hneigh] with z hz
    exact standardChartInverse_mul_standardChart S Q p q lift z hz
  · dsimp only [G, K]
    rw [standardChart_eq_localProductLift S Q p q lift y hx,
      standardChartInverse_eq_localProductLift S Q p q lift y hx]
    apply ContinuousLinearMap.ext
    intro z
    exact (standardActionL2 S _).apply_symm_apply z
  · intro t
    filter_upwards [hneigh, (chartOverlap_isOpen (I := 𝓘(ℝ,E)) p q).mem_nhds hy]
      with z hz hz'
    exact correctedConnection_affine_refined S Q D t p q lift z hz' hz

end
end QuaternionicSymmetry.QuaternionicManifoldCorrectedGaugeGerm
