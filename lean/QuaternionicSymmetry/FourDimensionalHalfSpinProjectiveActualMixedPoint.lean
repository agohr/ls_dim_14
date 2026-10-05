import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedMobiusPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors

/-! The actual adapted-frame transition carries source `[1:z]` into
target `[w:1]` by the mixed matrix fraction on its genuine refined lift
neighborhood, even when one of the two chart-overlap coordinates vanishes. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedPoint

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinSmoothLocalFactors
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveMixedMobiusPoint
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actualTransition_mixedPoint (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : mixedDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0) :
    spinorTransition Q (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
      (affineSpinorPoint z) =
    secondAffineSpinorPoint
      (mixedMobius (halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z) := by
  obtain ⟨a, b, ha, _, _, hproj, _⟩ :=
    local_factors_clifford Q (achart ℍ p) (achart ℍ q) lift
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx
  rw [hproj]
  have hmat : halfSpinMatrix (a : ℍ) =
      halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y) :=
    congrArg halfSpinMatrix ha
  have hden' : mixedDen (halfSpinMatrix (a : ℍ)) z ≠ 0 := by
    rwa [hmat]
  rw [projectiveHalfSpin_mixedPoint a z hden', hmat]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedPoint
