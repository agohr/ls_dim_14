import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInjective
import QuaternionicSymmetry.FourDimensionalExteriorUnitInverse

/-! Explicit local coefficient extraction from native alternating forms.
It uses the first three basis-pair evaluations in an actual smooth tangent
frame, so it can later serve as a jointly smooth inverse chart. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientExtraction

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorUnitInverse
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeExteriorComparison
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldTwistorCoefficientSphere
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

/-- The first three normalized frame-pair evaluations of a native form. -/
def nativeCoefficientRaw (i : atlas E M) (x : M)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) : Fin 3 → ℝ :=
  fun t => Real.sqrt 2 * α ![
    Q.frames.fromFrame i x ((localBasis Q hdim i) 0),
    Q.frames.fromFrame i x ((localBasis Q hdim i) (t.succ))]

theorem nativeCoefficientRaw_map (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : geometricSphere) :
    nativeCoefficientRaw Q hdim i x (nativeSphereForm Q i (x,a)) =
      (EuclideanSpace.equiv (Fin 3) ℝ) a.1 := by
  let b := localBasis Q hdim i
  let c := (EuclideanSpace.equiv (Fin 3) ℝ) a.1
  let η : TwoForm E := (Real.sqrt 2)⁻¹ •
    operatorForm b
      (VectorBundleFrameTransitions.QuaternionicFrameReduction.synth
        (Q.reduction.Q i) c)
  have hη : inverseCoefficients b η = c :=
    inverseCoefficients_normalized_synth
      (Q.reduction.Q i) hdim (unit : E) unit_norm c
  funext t
  have h := nativeSphereForm_evaluate Q hdim i x hi a
    (Q.frames.fromFrame i x (b 0))
    (Q.frames.fromFrame i x (b (t.succ)))
  rw [Q.frames.to_from i x hi, Q.frames.to_from i x hi] at h
  have hc := congrFun hη t
  change Real.sqrt 2 *
      nativeSphereForm Q i (x,a)
        ![Q.frames.fromFrame i x (b 0),
          Q.frames.fromFrame i x (b t.succ)] = c t
  rw [h]
  fin_cases t <;>
    simpa [inverseCoefficients, firstThree, coordinates,
      Pi.smul_apply, nativeCoefficientRaw, η, c, b,
      Fin.castLE] using hc

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientExtraction
