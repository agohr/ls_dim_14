import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualGauge
import QuaternionicSymmetry.FourDimensionalHalfSpinConnectionHopfMatch
import QuaternionicSymmetry.FourDimensionalHalfSpinQuaternionCoordinates

/-! Local horizontal spinor directions agree infinitesimally with the
independently defined rank-three sphere connection under the literal Hopf
formula.  This is a statement on representatives, prior to global tangent
bundle descent. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHorizontalHopf

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinConnectionHopfMatch
  FourDimensionalHalfSpinHopfInfinitesimal
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinLieProjection
  QuaternionicUnitScalarIsometries
  ManifoldQuaternionicAdjointConnection
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- The actual complex two-component connection matrix is literally
left multiplication by the extracted quaternionic Lie coefficient. -/
theorem fromSpinor_spinorMatrixForm (p : M) (y u : ℍ)
    (s : Fin 2 → ℂ) :
    fromSpinor (spinorMatrixForm Q D p y u *ᵥ s) =
      leftSpinorForm Q D p y u * fromSpinor s := by
  exact fromSpinor_halfSpinMatrix _ s

/-- The negative spinor connection direction maps to the negative of the
actual induced sphere connection direction.  Thus both independently
defined local horizontal graphs have the same Hopf infinitesimal action. -/
theorem horizontal_hopf_derivative (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target)
    (s : Fin 2 → ℂ) (a : Fin 3 → ℝ)
    (hs : quaternionHopf (fromSpinor s) = pureScalar a) :
    fderiv ℝ quaternionHopf (fromSpinor s)
      (fromSpinor (-(spinorMatrixForm Q D p y u *ᵥ s))) =
      -pureScalar (inducedForm Q D p y u a) := by
  change (fderiv ℝ quaternionHopf (fromSpinor s))
    (spinorQuaternionEquiv (-(spinorMatrixForm Q D p y u *ᵥ s))) = _
  rw [map_neg]
  change (fderiv ℝ quaternionHopf (fromSpinor s))
    (-fromSpinor (spinorMatrixForm Q D p y u *ᵥ s)) = _
  rw [fromSpinor_spinorMatrixForm Q D p y u]
  have h := leftSpinorForm_hopf_derivative Q D p y u hy (fromSpinor s) a hs
  rw [map_neg]
  exact congrArg Neg.neg h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHorizontalHopf
