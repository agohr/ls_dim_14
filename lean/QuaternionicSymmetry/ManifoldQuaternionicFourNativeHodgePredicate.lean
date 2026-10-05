import QuaternionicSymmetry.ManifoldQuaternionicFourNativeExteriorLiteral
import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSurjective

/-! The image-defined native sphere equals the literal reversed-orientation
Hodge-minus eigenvector/unit-norm predicate on its exterior representative.
The representative is computed from the native form by the canonical exterior
pairing after the actual quaternionic frame gauge. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeHodgePredicate

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorQuaternionicUnitSphere
open FourDimensionalExteriorQuaternionicUnitSurjective
open FourDimensionalExteriorHodgeOrientationFlip
open ManifoldQuaternionicFourNativeExteriorLiteral
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeExteriorComparison
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance

/-- Actual exterior representative in the quaternionic frame at `x`. -/
def nativeFrameExterior (i : atlas E M) (x : M)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) : TwoForm E :=
  nativeExterior (localBasis Q hdim i)
    (α.compContinuousLinearMap (Q.frames.fromFrame i x))

theorem nativeFrameExterior_evaluate (i : atlas E M) (x : M)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) (v w : E) :
    BilinearExterior.evaluate v w (nativeFrameExterior Q hdim i x α) =
      α ![Q.frames.fromFrame i x v,Q.frames.fromFrame i x w] := by
  rw [nativeFrameExterior, nativeExterior_evaluate,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext t
  fin_cases t <;> rfl

theorem nativeFrameExterior_sphereForm (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : coefficientSphere) :
    nativeFrameExterior Q hdim i x
      (nativeSphereForm Q i (x,coefficientSphereHomeomorph a)) =
      (Real.sqrt 2)⁻¹ • operatorForm (localBasis Q hdim i)
        (VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
          (Q.reduction.Q i) a.1) := by
  apply ExteriorDuality.twoform_ext (localBasis Q hdim i)
  intro v w
  rw [nativeFrameExterior_evaluate,
    nativeSphereForm_evaluate Q hdim i x hi]
  rw [Q.frames.to_from i x hi, Q.frames.to_from i x hi]
  rfl

/-- Literal reversed-orientation Hodge-minus equation and unit six-coordinate
Euclidean norm, calculated from the native form in an actual frame. -/
def nativeNegativeUnitPredicate (i : atlas E M) (x : M) :
    Set (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  {α | frameStar
      (FourDimensionalExteriorHodgeOrientationFlip.swap01
        (FourDimensionalQuaternionicHodgeFrame.frameBasis
          (Q.reduction.Q i) hdim (unit : E) unit_norm))
        (nativeFrameExterior Q hdim i x α) =
          -(nativeFrameExterior Q hdim i x α) ∧
      coordinateSquare (coordinates (localBasis Q hdim i)
        (nativeFrameExterior Q hdim i x α)) = 1}

theorem nativeLocalSphereSet_iff_hodge (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) :
    α ∈ nativeLocalSphereSet Q i x ↔
      α ∈ nativeNegativeUnitPredicate Q hdim i x := by
  constructor
  · rintro ⟨a,rfl⟩
    change _ ∧ _
    rw [nativeFrameExterior_sphereForm Q hdim i x hi a]
    exact normalized_synth_in_negativeUnitHalf
      (Q.reduction.Q i) hdim (unit : E) unit_norm a.1 a.2
  · intro hα
    have hpred : frameStar
        (swap01 (FourDimensionalQuaternionicHodgeFrame.frameBasis
          (Q.reduction.Q i) hdim (unit : E) unit_norm))
          (nativeFrameExterior Q hdim i x α) =
          -(nativeFrameExterior Q hdim i x α) ∧
        coordinateSquare (coordinates (localBasis Q hdim i)
          (nativeFrameExterior Q hdim i x α)) = 1 := hα
    let β : negativeUnitHalf
        (FourDimensionalQuaternionicHodgeFrame.frameBasis
          (Q.reduction.Q i) hdim (unit : E) unit_norm) :=
      ⟨nativeFrameExterior Q hdim i x α, hpred⟩
    obtain ⟨a,ha,hβ⟩ := negativeUnitHalf_surjective
      (Q.reduction.Q i) hdim (unit : E) unit_norm β
    let s : coefficientSphere := ⟨a,ha⟩
    refine ⟨s, ?_⟩
    have hframe : nativeFrameExterior Q hdim i x α =
        nativeFrameExterior Q hdim i x
          (nativeSphereForm Q i (x,coefficientSphereHomeomorph s)) := by
      rw [nativeFrameExterior_sphereForm Q hdim i x hi s]
      exact hβ.symm
    apply ContinuousAlternatingMap.ext
    intro v
    have hv : v = ![v 0,v 1] := by
      funext t
      fin_cases t <;> rfl
    rw [hv]
    have he := congrArg (BilinearExterior.evaluate
      (Q.frames.toFrame i x (v 0))
      (Q.frames.toFrame i x (v 1))) hframe
    rw [nativeFrameExterior_evaluate,
      nativeFrameExterior_evaluate,
      Q.frames.from_to i x hi,Q.frames.from_to i x hi] at he
    exact he

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeHodgePredicate
