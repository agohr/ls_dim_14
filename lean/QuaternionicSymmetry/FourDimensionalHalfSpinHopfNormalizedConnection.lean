import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHorizontalHopf

/-! The genuine normalized Hopf quaternion carries the actual negative
spinor-matrix connection direction to the negative induced rank-three
connection direction, still on a nonzero homogeneous representative. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedConnection

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinHopfNormalizedPath
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfNormalizedDerivative
  FourDimensionalHalfSpinProjectiveHorizontalHopf
  FourDimensionalHalfSpinConnectionHopfMatch
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinLieProjection
  QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries
  ManifoldQuaternionicAdjointConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def normalizedSpinorHopf (s : Spinor) : ℍ :=
  (Quaternion.normSq (fromSpinor s))⁻¹ • hopfRaw s

theorem normalizedSpinorHopf_eq (s : Spinor) :
    normalizedSpinorHopf s = normalizedQuaternionHopf (fromSpinor s) := rfl

theorem normalizedSpinorHopf_fderiv (s : Spinor) (hs : s ≠ 0)
    (v : Spinor) :
    fderiv ℝ normalizedSpinorHopf s v =
      fderiv ℝ normalizedQuaternionHopf (fromSpinor s) (fromSpinor v) := by
  have hq : fromSpinor s ≠ 0 := by
    intro hz
    apply hs
    apply fromSpinor_injective
    simpa [fromSpinor] using hz
  let L : Spinor →L[ℝ] ℍ :=
    spinorQuaternionEquiv.toLinearMap.toContinuousLinearMap
  have hd := fderiv_comp s
    (normalizedQuaternionHopf_differentiableAt (fromSpinor s) hq) L.differentiableAt
  change fderiv ℝ (normalizedQuaternionHopf ∘ L) s =
    (fderiv ℝ normalizedQuaternionHopf (fromSpinor s)).comp (fderiv ℝ L s) at hd
  rw [L.fderiv] at hd
  change fderiv ℝ normalizedSpinorHopf s =
    (fderiv ℝ normalizedQuaternionHopf (fromSpinor s)).comp L at hd
  exact congrArg (fun T : Spinor →L[ℝ] ℍ => T v) hd

theorem normalizedSpinorHopf_horizontal_derivative
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target)
    (s : Spinor) (hs : s ≠ 0) :
    fderiv ℝ normalizedSpinorHopf s
      (-(spinorMatrixForm Q D p y u *ᵥ s)) =
      -pureScalar (inducedForm Q D p y u (hopfSphere s hs).1) := by
  let a := leftSpinorForm Q D p y u
  let q := fromSpinor s
  have hq : q ≠ 0 := by
    intro hz
    apply hs
    apply fromSpinor_injective
    simpa [q, fromSpinor] using hz
  have hrep : fromSpinor (-(spinorMatrixForm Q D p y u *ᵥ s)) =
      -(a*q) := by
    change spinorQuaternionEquiv (-(spinorMatrixForm Q D p y u *ᵥ s)) = _
    rw [map_neg]
    change -(fromSpinor (spinorMatrixForm Q D p y u *ᵥ s)) = _
    rw [fromSpinor_spinorMatrixForm Q D p y u]
  rw [normalizedSpinorHopf_fderiv s hs, hrep, map_neg]
  rw [normalizedQuaternionHopf_left_infinitesimal a q
    (leftSpinorForm_re Q D p y u) hq]
  have hHopf : normalizedQuaternionHopf q =
      pureScalar (hopfSphere s hs).1 := by
    rw [pureScalar_hopfSphere]
    exact (hopfQuaternion_eq_ratio s hs).symm
  rw [hHopf]
  exact congrArg Neg.neg
    (leftSpinorForm_hopf_commutator Q D p y u hy (hopfSphere s hs).1).symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedConnection
