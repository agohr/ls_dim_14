import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineHorizontal

/-! The affine-coordinate derivative of the normalized Hopf quaternion is
the representative differential on the genuine affine spinor lift. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineDerivative

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfNormalizedConnection
  FourDimensionalHalfSpinHopfScalarDerivative
  FourDimensionalHalfSpinHopfAffineHorizontal
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinHopfSphere
  ManifoldQuaternionicAdjointConnection
  QuaternionicUnitScalarIsometries

noncomputable section

def affineSpinorLift (z : ℂ) : Spinor := ![1,z]

private def affineSpinorLinear : ℂ →L[ℝ] Spinor :=
  ContinuousLinearMap.pi (fun j : Fin 2 =>
    if j = 0 then 0 else ContinuousLinearMap.id ℝ ℂ)

private theorem affineSpinorLift_eq (z : ℂ) :
    affineSpinorLift z = ![1,0] + affineSpinorLinear z := by
  ext j
  fin_cases j <;> simp [affineSpinorLift, affineSpinorLinear]

private theorem affineSpinorLift_hasFDerivAt (z : ℂ) :
    HasFDerivAt affineSpinorLift affineSpinorLinear z := by
  convert (hasFDerivAt_const (𝕜 := ℝ) (![1,0] : Spinor) z).add
    affineSpinorLinear.hasFDerivAt using 1
  · funext w; exact affineSpinorLift_eq w
  · simp

private theorem affineSpinorLift_fderiv (z w : ℂ) :
    fderiv ℝ affineSpinorLift z w = ![0,w] := by
  rw [(affineSpinorLift_hasFDerivAt z).fderiv]
  ext j
  fin_cases j <;> simp [affineSpinorLinear]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem normalizedSpinorHopf_affine_fderiv
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    fderiv ℝ (normalizedSpinorHopf ∘ affineSpinorLift) z
      (-(projectiveConnectionGenerator Q D p y u z)) =
      -pureScalar (inducedForm Q D p y u
        (hopfSphere ![1,z] (by simp)).1) := by
  have hcomp := fderiv_comp z
    (by simpa [affineSpinorLift] using
      normalizedSpinorHopf_differentiableAt ![1,z] (by simp))
    (affineSpinorLift_hasFDerivAt z).differentiableAt
  have hv := congrArg (fun L : ℂ →L[ℝ] ℍ =>
    L (-(projectiveConnectionGenerator Q D p y u z))) hcomp
  simp only [ContinuousLinearMap.comp_apply, affineSpinorLift_fderiv] at hv
  exact hv.trans (normalizedSpinorHopf_affine_horizontal Q D p y u hy z)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineDerivative
