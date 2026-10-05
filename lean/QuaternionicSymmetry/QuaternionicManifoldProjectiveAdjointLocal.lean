import QuaternionicSymmetry.QuaternionicManifoldStandardLocalOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The standard adjoint coordinate change is smooth on each refined
overlap and independent of the selected local product lift. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointLocal

open VectorBundleFrameTransitions
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldSignedLocalLifts
  QuaternionicManifoldStandardLocalOperator
  QuaternionicProjectiveStandardL2
  QuaternionicProjectiveStandardAdjoint
open scoped ContDiff Manifold Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

abbrev W := StandardSpace (E := E)
abbrev A := StandardEnd (E := E)

def localAdjointOperator (i j : atlas E M) (q : unitary ℍ) (y : M) :
    A (E := E) →L[ℝ] A (E := E) :=
  (((ContinuousLinearMap.compL ℝ (W (E := E)) (W (E := E))
      (W (E := E))).flip)
      ((localStandardOperator S Q i j q y).adjoint)).comp
    ((ContinuousLinearMap.compL ℝ (W (E := E)) (W (E := E))
      (W (E := E)))
      (localStandardOperator S Q i j q y))

theorem continuousOn_localAdjointOperator (i j : atlas E M) (q : unitary ℍ) :
    ContinuousOn
      (localAdjointOperator S Q i j q)
      (liftNeighborhood Q i j q) := by
  have hG := (smooth_localStandardOperator S Q i j q).continuousOn
  have hGstar : ContinuousOn
      (fun y : M => (localStandardOperator S Q i j q y).adjoint)
      (liftNeighborhood Q i j q) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hG
  have hleft : ContinuousOn
      (fun y : M => (ContinuousLinearMap.compL ℝ (W (E := E))
        (W (E := E)) (W (E := E)))
        (localStandardOperator S Q i j q y))
      (liftNeighborhood Q i j q) :=
    (ContinuousLinearMap.compL ℝ (W (E := E))
      (W (E := E)) (W (E := E))).continuous.comp_continuousOn hG
  have hright : ContinuousOn
      (fun y : M => ((ContinuousLinearMap.compL ℝ (W (E := E))
        (W (E := E)) (W (E := E))).flip)
        ((localStandardOperator S Q i j q y).adjoint))
      (liftNeighborhood Q i j q) :=
    ((ContinuousLinearMap.compL ℝ (W (E := E))
      (W (E := E)) (W (E := E))).flip).continuous.comp_continuousOn hGstar
  exact hright.clm_comp hleft

set_option maxHeartbeats 1000000 in
private theorem standardAdjoint_comp_adjoint
    (p : QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ) :
    (((ContinuousLinearMap.compL ℝ (W (E := E)) (W (E := E))
      (W (E := E))).flip)
        ((standardActionL2 S p).toContinuousLinearMap.adjoint)).comp
      ((ContinuousLinearMap.compL ℝ (W (E := E)) (W (E := E))
        (W (E := E)))
        (standardActionL2 S p).toContinuousLinearMap) =
      standardAdjoint S p := by
  ext B z
  have hadj := (standardIsometryL2 S p).adjoint_eq_symm
  change standardActionL2 S p
    (B ((standardActionL2 S p).toContinuousLinearMap.adjoint z)) =
      standardAdjoint S p B z
  rw [standardAdjoint_apply]
  exact congrArg (fun T : A (E := E) =>
    standardActionL2 S p (B (T z))) hadj

theorem localAdjointOperator_eq (i j : atlas E M)
    (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) :
    localAdjointOperator S Q i j q y =
      standardAdjoint S (localProductLift S Q i j q y hy) := by
  unfold localAdjointOperator
  rw [localStandardOperator_eq S Q i j q y hy]
  exact standardAdjoint_comp_adjoint S _

end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointLocal
