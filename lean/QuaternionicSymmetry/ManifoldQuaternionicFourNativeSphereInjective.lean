import QuaternionicSymmetry.ManifoldQuaternionicFourNativeExteriorComparison
import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitInjective

/-! The local normalized native two-form parametrization is fiberwise
faithful, independently of its total-space topology. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInjective

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorQuaternionicUnitInjective
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeExteriorComparison
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

theorem nativeSphereForm_injective (hdim : Module.finrank ℝ E = 4)
    (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    Function.Injective (fun a : geometricSphere => nativeSphereForm Q i (x,a)) := by
  intro a c hac
  let b := localBasis Q hdim i
  let ηa : TwoForm E := (Real.sqrt 2)⁻¹ •
    operatorForm b (VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
      (Q.reduction.Q i) ((EuclideanSpace.equiv (Fin 3) ℝ) a.1))
  let ηc : TwoForm E := (Real.sqrt 2)⁻¹ •
    operatorForm b (VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
      (Q.reduction.Q i) ((EuclideanSpace.equiv (Fin 3) ℝ) c.1))
  have hforms : ηa = ηc := by
    apply ExteriorDuality.twoform_ext b
    intro v w
    have h := congrArg
      (fun α : E [⋀^Fin 2]→L[ℝ] ℝ =>
        α ![Q.frames.fromFrame i x v,Q.frames.fromFrame i x w]) hac
    change nativeSphereForm Q i (x,a)
        ![Q.frames.fromFrame i x v,Q.frames.fromFrame i x w] =
      nativeSphereForm Q i (x,c)
        ![Q.frames.fromFrame i x v,Q.frames.fromFrame i x w] at h
    rw [nativeSphereForm_evaluate Q hdim i x hi a,
      nativeSphereForm_evaluate Q hdim i x hi c] at h
    rw [Q.frames.to_from i x hi, Q.frames.to_from i x hi] at h
    exact h
  have hcoeff := normalized_operatorForm_synth_injective
    (Q.reduction.Q i) hdim (unit : E) unit_norm
      ((EuclideanSpace.equiv (Fin 3) ℝ) a.1)
      ((EuclideanSpace.equiv (Fin 3) ℝ) c.1) hforms
  apply Subtype.ext
  exact (EuclideanSpace.equiv (Fin 3) ℝ).injective hcoeff

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInjective
