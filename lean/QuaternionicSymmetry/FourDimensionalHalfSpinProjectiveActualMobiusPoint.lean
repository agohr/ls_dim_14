import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors

/-! The actual adapted quaternionic-frame projective transition agrees
with the explicit Möbius affine point on every refined local spin lift. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMobiusPoint

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinSmoothLocalFactors
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveMobiusPoint
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actualTransition_affinePoint (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : chartDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0) :
    spinorTransition Q (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
      (affineSpinorPoint z) =
    affineSpinorPoint
      (mobius (halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z) := by
  obtain ⟨a, b, ha, _, _, hproj, _⟩ :=
    local_factors_clifford Q (achart ℍ p) (achart ℍ q) lift
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx
  rw [hproj]
  have hmat : halfSpinMatrix (a : ℍ) =
      halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y) :=
    congrArg halfSpinMatrix ha
  have hden' : chartDen (halfSpinMatrix (a : ℍ)) z ≠ 0 := by
    rwa [hmat]
  rw [projectiveHalfSpin_affinePoint a z hden', hmat]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMobiusPoint
