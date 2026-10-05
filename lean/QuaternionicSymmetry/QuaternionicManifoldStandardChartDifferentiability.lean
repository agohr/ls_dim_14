import QuaternionicSymmetry.QuaternionicManifoldProductRepresentationPointwise

/-! Differentiability of both local standard operator gauges in actual
source chart coordinates. -/

namespace QuaternionicSymmetry.QuaternionicManifoldStandardChartDifferentiability

open scoped Manifold ContDiff Quaternion Topology
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldStandardMaurerIdentity
open QuaternionicManifoldProductGaugeDifferential
open QuaternionicManifoldProductRepresentationPointwise
open QuaternionicManifoldStandardLocalOperator
open QuaternionicProjectiveStandardL2
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem standardChart_differentiableAt (p : M) (i j : atlas E M)
    (lift : unitary ℍ) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q i j lift) :
    DifferentiableAt ℝ (standardChart S Q p i j lift) y := by
  exact differentiableAt_chartPullback
    (localStandardOperator S Q i j lift)
    (liftNeighborhood Q i j lift) (isOpen_liftNeighborhood Q i j lift)
    (smooth_localStandardOperator S Q i j lift) p y hy hx

theorem standardChartInverse_differentiableAt (p q : M)
    (lift : unitary ℍ) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    DifferentiableAt ℝ
      (standardChartInverse S Q p (achart E p) (achart E q) lift) y := by
  let G := standardChart S Q p (achart E p) (achart E q) lift
  let H := standardChartInverse S Q p (achart E p) (achart E q) lift
  have hG : DifferentiableAt ℝ G y :=
    standardChart_differentiableAt S Q p _ _ lift y hy hx
  let L : (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) →L[ℝ]
      (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearMap
  have hAdj : DifferentiableAt ℝ (fun z => (G z).adjoint) y := by
    simpa only [Function.comp_def, L] using L.differentiableAt.comp y hG
  have hneigh : ∀ᶠ z in 𝓝 y,
      (extChartAt 𝓘(ℝ, E) p).symm z ∈
        liftNeighborhood Q (achart E p) (achart E q) lift :=
    (continuousAt_extChartAt_symm'' hy).preimage_mem_nhds
      ((isOpen_liftNeighborhood Q _ _ lift).mem_nhds hx)
  have heq : H =ᶠ[𝓝 y] (fun z => (G z).adjoint) := by
    filter_upwards [hneigh] with z hz
    change standardChartInverse S Q p (achart E p) (achart E q) lift z =
      (standardChart S Q p (achart E p) (achart E q) lift z).adjoint
    rw [standardChartInverse_eq_localProductLift S Q p q lift z hz,
      standardChart_eq_localProductLift S Q p q lift z hz]
    exact (standardIsometryL2 S
      (QuaternionicManifoldSignedLocalLifts.localProductLift S Q
        (achart E p) (achart E q) lift
        ((extChartAt 𝓘(ℝ, E) p).symm z) hz)).adjoint_eq_symm.symm
  exact hAdj.congr_of_eventuallyEq heq

end
end QuaternionicSymmetry.QuaternionicManifoldStandardChartDifferentiability
