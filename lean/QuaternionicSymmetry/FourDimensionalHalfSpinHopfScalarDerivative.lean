import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveDescent

/-! The normalized Hopf map kills infinitesimal complex rescaling of a
nonzero homogeneous spinor.  This is the differential needed to descend
the representative-level connection calculation to a projective tangent. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfScalarDerivative

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfNormalizedPath
  FourDimensionalHalfSpinHopfNormalizedDerivative
  FourDimensionalHalfSpinHopfNormalizedConnection
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinQuaternionCoordinates
open Filter

noncomputable section

theorem normalizedSpinorHopf_smul (c : ℂ) (hc : c ≠ 0)
    (s : Spinor) (hs : s ≠ 0) :
    normalizedSpinorHopf (c • s) = normalizedSpinorHopf s := by
  simpa only [hopfQuaternion_eq_ratio, normalizedSpinorHopf] using
    hopfQuaternion_smul c hc s hs

theorem normalizedSpinorHopf_differentiableAt (s : Spinor) (hs : s ≠ 0) :
    DifferentiableAt ℝ normalizedSpinorHopf s := by
  have hq : fromSpinor s ≠ 0 := by
    intro hz
    apply hs
    apply fromSpinor_injective
    simpa [fromSpinor] using hz
  exact (normalizedQuaternionHopf_differentiableAt (fromSpinor s) hq).comp
    s spinorQuaternionEquiv.toLinearMap.toContinuousLinearMap.differentiableAt

theorem normalizedSpinorHopf_scalar_derivative
    (s : Spinor) (hs : s ≠ 0) (c : ℂ) :
    fderiv ℝ normalizedSpinorHopf s (c • s) = 0 := by
  let L : ℂ →L[ℝ] Spinor :=
    (ContinuousLinearMap.id ℝ ℂ).smulRight s
  have hL : HasFDerivAt (fun d : ℂ => d • s) L (1 : ℂ) := by
    convert ((hasFDerivAt_id (𝕜 := ℝ) (1 : ℂ)).smul_const s) using 1
  have hfun : (fun d : ℂ => normalizedSpinorHopf (d • s)) =ᶠ[𝓝 (1 : ℂ)]
      fun _ => normalizedSpinorHopf s := by
    filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)] with d hd
    exact normalizedSpinorHopf_smul d hd s hs
  have hcomp := fderiv_comp (1 : ℂ)
    (by simpa using normalizedSpinorHopf_differentiableAt s hs)
    hL.differentiableAt
  simp only [one_smul, Function.comp_def] at hcomp
  change fderiv ℝ (fun d : ℂ => normalizedSpinorHopf (d • s)) 1 =
    (fderiv ℝ normalizedSpinorHopf s).comp (fderiv ℝ (fun d : ℂ => d • s) 1)
    at hcomp
  rw [hfun.fderiv_eq, hL.fderiv] at hcomp
  have hzero : fderiv ℝ (fun _ : ℂ => normalizedSpinorHopf s) (1 : ℂ) = 0 := by
    simp
  rw [hzero] at hcomp
  have hc := congrArg (fun T : ℂ →L[ℝ] ℍ => T c) hcomp
  simpa [L] using hc.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfScalarDerivative
