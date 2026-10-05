import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMobiusPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseComplex

/-! Actual raw-chart antipodal horizontal base-complex covariance written
in the same CP¹ affine Möbius coordinates as the projective connection. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseMobius

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjectiveActualBaseComplex
  FourDimensionalHalfSpinProjectiveActualMobiusPoint
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinAntipodalVerticalSign
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem affineSpinorPoint_hopf (z : ℂ) :
    projectiveHopf (affineSpinorPoint z) =
      hopfSphere ![1,z] (by simp) := by
  unfold affineSpinorPoint
  exact projectiveHopf_mk _ _

theorem actual_antipodal_baseComplex_mobius (p q : M)
    (lift : unitary ℍ) (y u : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : chartDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0) :
    let w := mobius
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z
    fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y
      (chartBaseComplex Q p y
        (antipodalCoefficient (hopfSphere ![1,z] (by simp))) u) =
      chartBaseComplex Q q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
        (antipodalCoefficient (hopfSphere ![1,w] (by simp)))
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u) := by
  dsimp
  have h := actual_projective_antipodal_base_complex_overlap Q p q y hy
    hx.1.1 hx.1.2 (affineSpinorPoint z) u
  rw [actualTransition_affinePoint Q p q lift y hx z hden] at h
  rw [affineSpinorPoint_hopf, affineSpinorPoint_hopf] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseMobius
