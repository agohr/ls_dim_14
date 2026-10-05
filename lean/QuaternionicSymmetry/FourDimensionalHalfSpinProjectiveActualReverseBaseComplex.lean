import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReversePoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseMobius

/-! The actual raw adapted-base complex operator is covariant from
second projective affine source to first affine target. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReverseBaseComplex

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjectiveActualBaseComplex
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
  FourDimensionalHalfSpinProjectiveActualReversePoint
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveMobiusAction
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

theorem actual_reverse_antipodal_baseComplex_mobius (p q : M)
    (lift : unitary ℍ) (y u : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : reverseDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0) :
    let z := reverseMobius
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w
    fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y
      (chartBaseComplex Q p y
        (antipodalCoefficient (hopfSphere ![w,1] (by simp))) u) =
      chartBaseComplex Q q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
        (antipodalCoefficient (hopfSphere ![1,z] (by simp)))
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u) := by
  dsimp
  have h := actual_projective_antipodal_base_complex_overlap Q p q y hy
    hx.1.1 hx.1.2 (secondAffineSpinorPoint w) u
  rw [actualTransition_reversePoint Q p q lift y hx w hden] at h
  rw [secondAffineSpinorPoint_hopf,
    affineSpinorPoint_hopf] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReverseBaseComplex
