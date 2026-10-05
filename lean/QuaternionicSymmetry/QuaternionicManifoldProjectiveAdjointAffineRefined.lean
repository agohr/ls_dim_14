import QuaternionicSymmetry.QuaternionicManifoldStandardAffineOverlap
import QuaternionicSymmetry.QuaternionicManifoldStandardChartDifferentiability
import QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeDescent
import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointConnection

/-! The induced adjoint connection obeys the affine gauge law on each
actual refined overlap. Its gauge is conjugation by the locally lifted
standard operator. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointAffineRefined

open scoped Manifold ContDiff Quaternion Topology
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicManifoldStandardChartDifferentiability
open QuaternionicManifoldProductRepresentationPointwise
open QuaternionicManifoldStandardAffineOverlap
open QuaternionicProjectiveAdjointGaugeDescent
open QuaternionicProjectiveAdjointGaugeDerivative
open QuaternionicManifoldProjectiveAdjointConnection
open QuaternionicManifoldProjectiveStandardConnection
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

set_option maxHeartbeats 800000 in
theorem adjointConnection_affine_refined (p q : M) (lift : unitary ℍ)
    (y : E) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    let G := standardChart S Q p (achart E p) (achart E q) lift
    let K := standardChartInverse S Q p (achart E p) (achart E q) lift
    adjointConnection S Q D p y =
      LocalConnectionGauge.transform
        (LocalConnectionCoordinatePullback.pullback
          (adjointConnection S Q D q)
          (chartTransition (I := 𝓘(ℝ, E)) p q))
        (conjugationGauge G K) (conjugationGauge K G) y := by
  dsimp
  let G := standardChart S Q p (achart E p) (achart E q) lift
  let K := standardChartInverse S Q p (achart E p) (achart E q) lift
  have hG : DifferentiableAt ℝ G y :=
    standardChart_differentiableAt S Q p _ _ lift y hy.1 hx
  have hK : DifferentiableAt ℝ K y :=
    standardChartInverse_differentiableAt S Q p q lift y hy.1 hx
  have hneigh : ∀ᶠ z in 𝓝 y,
      (extChartAt 𝓘(ℝ, E) p).symm z ∈
        liftNeighborhood Q (achart E p) (achart E q) lift :=
    (continuousAt_extChartAt_symm'' hy.1).preimage_mem_nhds
      ((isOpen_liftNeighborhood Q _ _ lift).mem_nhds hx)
  have hleft : (fun z => K z * G z) =ᶠ[𝓝 y]
      fun _ => 1 := by
    filter_upwards [hneigh] with z hz
    exact standardChartInverse_mul_standardChart S Q p q lift z hz
  have hleftx : K y * G y = 1 := hleft.self_of_nhds
  have hrightx : G y * K y = 1 := by
    change standardChart S Q p (achart E p) (achart E q) lift y *
      standardChartInverse S Q p (achart E p) (achart E q) lift y = 1
    rw [standardChart_eq_localProductLift S Q p q lift y hx,
      standardChartInverse_eq_localProductLift S Q p q lift y hx]
    apply ContinuousLinearMap.ext
    intro z
    exact (QuaternionicProjectiveStandardL2.standardActionL2 S
      (QuaternionicManifoldSignedLocalLifts.localProductLift S Q
        (achart E p) (achart E q) lift
        ((extChartAt 𝓘(ℝ, E) p).symm y) hx)).apply_symm_apply z
  have hStd := standardConnection_affine_refined S Q D p q lift y hy hx
  apply ContinuousLinearMap.ext
  intro u
  have hAd := adjoint_transform
    (LocalConnectionCoordinatePullback.pullback
      (standardConnection S Q D q)
      (chartTransition (I := 𝓘(ℝ, E)) p q))
    G K y u hG hK hleft hleftx hrightx
  change adjointForm (standardConnection S Q D p) y u =
    LocalConnectionGauge.transform
      (adjointForm (LocalConnectionCoordinatePullback.pullback
        (standardConnection S Q D q)
        (chartTransition (I := 𝓘(ℝ, E)) p q)))
      (conjugationGauge G K) (conjugationGauge K G) y u
  calc
    adjointForm (standardConnection S Q D p) y u =
        adjointForm (LocalConnectionGauge.transform
          (LocalConnectionCoordinatePullback.pullback
            (standardConnection S Q D q)
            (chartTransition (I := 𝓘(ℝ, E)) p q)) G K) y u := by
      exact congrArg
        (fun A : QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E) =>
          (ad (R := QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E))) A)
        (congrArg (fun F : E →L[ℝ]
          QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E) => F u) hStd)
    _ = _ := hAd

end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointAffineRefined
