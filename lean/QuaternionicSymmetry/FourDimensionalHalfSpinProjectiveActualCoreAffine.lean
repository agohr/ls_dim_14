import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFiberChartMFDeriv
import QuaternionicSymmetry.FourDimensionalHalfSpinActualTransitionSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative

/-! The affine Möbius expression is the literal coordinate of the
independently defined projective bundle core transition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualCoreAffine

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinActualTransitionSmooth
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinProjectiveActualMobiusPoint
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldQuaternionicConnection
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actual_core_affine_transition (p q : M) (lift : unitary ℍ)
    (y : ℍ)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : chartDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0) :
    ((projectiveChart 1 0)
      (spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y, affineSpinorPoint z))) 0 =
      mobius (halfSpinMatrix
        (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z := by
  have hcore : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y, affineSpinorPoint z) =
      spinorTransition Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
        (affineSpinorPoint z) := by
    dsimp [spinorCoordChange]
    rw [dif_pos ⟨hx.1.1,hx.1.2⟩]
  rw [hcore, actualTransition_affinePoint Q p q lift y hx z hden]
  rw [affineSpinorPoint_eq_projectiveChart]
  rw [(projectiveChart 1 0).right_inv (by rw [projectiveChart_target]; trivial)]
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualCoreAffine
