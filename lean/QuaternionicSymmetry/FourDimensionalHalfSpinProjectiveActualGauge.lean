import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinMatrixConnection

/-! The Möbius projective-connection chain rule on an actual refined
quaternionic adapted-frame overlap.  The local unit lift is only used on
its genuine open neighborhood; no global spin choice is made. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualGauge

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinMatrix
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldProductGaugeDifferential
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- The literal projective horizontal coefficient transforms by the
Möbius tangent derivative plus the projectivized moving-frame derivative.
`B` is the p-chart connection and `A` the q-chart connection. -/
theorem actual_projective_gauge_chain (p q : M) (lift : unitary ℍ)
    (y u : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := halfSpinMatrix (r y)
    let A := spinorMatrixForm Q D q
      (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
      (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u)
    let B := spinorMatrixForm Q D p y u
    let C := fderiv ℝ (fun x => halfSpinMatrix (r x)) y u
    chartDen G z ≠ 0 →
      deriv (mobius G) z * affineGenerator B z =
        affineGenerator A (mobius G z) +
          deriv (varyingMobius G C z) 0 := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G := halfSpinMatrix (r y)
  let A := spinorMatrixForm Q D q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
    (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u)
  let B := spinorMatrixForm Q D p y u
  let C := fderiv ℝ (fun x => halfSpinMatrix (r x)) y u
  intro hden
  have hnorm : Quaternion.normSq (r y) = 1 := by
    change Quaternion.normSq
      (scalarLiftRaw Q (achart ℍ p) (achart ℍ q) lift
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y)) = 1
    exact (scalarLiftRaw_valid Q leftLineStructure
      (achart ℍ p) (achart ℍ q) lift _ hx).1
  have hmat : G * halfSpinMatrix (star (r y)) = 1 := by
    dsimp [G]
    rw [← halfSpinMatrix_mul, Quaternion.self_mul_star, hnorm]
    simpa using halfSpinMatrix_one
  have hform : B = halfSpinMatrix (star (r y)) * (A * G + C) := by
    exact spinorMatrixForm_affine_refined Q D p q lift y u hy hx
  have hG : G * B = A * G + C := by
    rw [hform, ← mul_assoc, hmat, one_mul]
  exact affine_gauge_chain G A B C z hG hden

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualGauge
