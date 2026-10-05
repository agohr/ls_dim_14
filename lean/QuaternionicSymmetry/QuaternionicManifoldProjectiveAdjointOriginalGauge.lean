import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointAffineRefined
import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointCore

/-! The original adjoint transition agrees locally with conjugation by any
smooth product lift. Its reverse transition is the inverse conjugation. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointOriginalGauge

open scoped Manifold ContDiff Quaternion Topology
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicManifoldProductRepresentationPointwise
open QuaternionicManifoldProjectiveAdjointCore
open QuaternionicManifoldProjectiveAdjointLocal
open QuaternionicProjectiveAdjointGaugeDerivative
open QuaternionicProjectiveStandardL2
open ManifoldQuaternionicConnection
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardAdjoint.StandardEnd (E := E)) := inferInstance

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

private theorem standardChartInverse_eq_adjoint (p q : M) (lift : unitary ℍ)
    (y : E)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardChartInverse S Q p (achart E p) (achart E q) lift y =
      (standardChart S Q p (achart E p) (achart E q) lift y).adjoint := by
  rw [standardChartInverse_eq_localProductLift S Q p q lift y hx,
    standardChart_eq_localProductLift S Q p q lift y hx]
  exact (standardIsometryL2 S
    (QuaternionicManifoldSignedLocalLifts.localProductLift S Q
      (achart E p) (achart E q) lift
      ((extChartAt 𝓘(ℝ, E) p).symm y) hx)).adjoint_eq_symm.symm

set_option maxHeartbeats 800000 in
theorem projectiveChart_eq_conjugation (p q : M) (lift : unitary ℍ)
    (y : E)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    projectiveCoordChange S Q (achart E p) (achart E q)
      ((extChartAt 𝓘(ℝ, E) p).symm y) =
    conjugationGauge
      (standardChart S Q p (achart E p) (achart E q) lift)
      (standardChartInverse S Q p (achart E p) (achart E q) lift) y := by
  rw [projectiveCoordChange_eq_local S Q _ _ lift _ hx]
  apply ContinuousLinearMap.ext
  intro B
  rw [conjugationGauge_apply, standardChartInverse_eq_adjoint S Q p q lift y hx]
  rfl

set_option maxHeartbeats 800000 in
theorem projectiveChartReverse_eq_conjugation (p q : M) (lift : unitary ℍ)
    (y : E)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    projectiveCoordChange S Q (achart E q) (achart E p)
      ((extChartAt 𝓘(ℝ, E) p).symm y) =
    conjugationGauge
      (standardChartInverse S Q p (achart E p) (achart E q) lift)
      (standardChart S Q p (achart E p) (achart E q) lift) y := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  let G := standardChart S Q p (achart E p) (achart E q) lift
  let K := standardChartInverse S Q p (achart E p) (achart E q) lift
  have hF := projectiveChart_eq_conjugation S Q p q lift y hx
  have hGF : G y * K y = 1 := by
    change standardChart S Q p (achart E p) (achart E q) lift y *
      standardChartInverse S Q p (achart E p) (achart E q) lift y = 1
    rw [standardChart_eq_localProductLift S Q p q lift y hx,
      standardChartInverse_eq_localProductLift S Q p q lift y hx]
    apply ContinuousLinearMap.ext
    intro z
    exact (standardActionL2 S
      (QuaternionicManifoldSignedLocalLifts.localProductLift S Q
        (achart E p) (achart E q) lift x hx)).apply_symm_apply z
  have hKG : K y * G y = 1 := standardChartInverse_mul_standardChart S Q p q lift y hx
  apply ContinuousLinearMap.ext
  intro B
  have hF' : projectiveCoordChange S Q (achart E p) (achart E q) x =
      conjugationGauge G K y := hF
  have hInv : conjugationGauge G K y
      (conjugationGauge K G y B) = B := by
    simp only [conjugationGauge_apply]
    calc
      G y * (K y * B * G y) * K y = (G y * K y) * B * (G y * K y) := by
        noncomm_ring
      _ = B := by rw [hGF]; simp
  calc
    projectiveCoordChange S Q (achart E q) (achart E p) x B =
        projectiveCoordChange S Q (achart E q) (achart E p) x
          (conjugationGauge G K y (conjugationGauge K G y B)) := by rw [hInv]
    _ = conjugationGauge K G y B := by
      rw [← hF', projectiveCoordChange_comp S Q
        (achart E p) (achart E q) (achart E p) x
        hx.1.1 hx.1.2 hx.1.1, projectiveCoordChange_self S Q
        (achart E p) x hx.1.1]

end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointOriginalGauge
