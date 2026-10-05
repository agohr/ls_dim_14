import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseMobius

/-! The actual raw adapted-base complex operator is covariant from the
first projective affine source into the second affine target, without an
overlap nonzero condition on either affine coordinate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedBaseComplex

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjectiveActualBaseComplex
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
  FourDimensionalHalfSpinProjectiveActualMixedPoint
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
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

theorem actual_mixed_antipodal_baseComplex_mobius (p q : M)
    (lift : unitary ℍ) (y u : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : mixedDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0) :
    let w := mixedMobius
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z
    fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y
      (chartBaseComplex Q p y
        (antipodalCoefficient (hopfSphere ![1,z] (by simp))) u) =
      chartBaseComplex Q q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
        (antipodalCoefficient (hopfSphere ![w,1] (by simp)))
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u) := by
  dsimp
  have h := actual_projective_antipodal_base_complex_overlap Q p q y hy
    hx.1.1 hx.1.2 (affineSpinorPoint z) u
  rw [actualTransition_mixedPoint Q p q lift y hx z hden] at h
  rw [affineSpinorPoint_hopf,
    secondAffineSpinorPoint_hopf] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedBaseComplex
