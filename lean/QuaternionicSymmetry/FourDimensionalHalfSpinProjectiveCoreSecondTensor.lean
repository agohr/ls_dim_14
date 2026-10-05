import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreSecondGerm
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondMFDeriv

/-! The literal second-to-second projective bundle-core coordinate
change intertwines the independent local AHS tensor under its actual
manifold derivative. This completes the four affine source/target cases
on refined adapted overlaps. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreSecondTensor

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveCoreSecondGerm
  FourDimensionalHalfSpinProjectiveActualSecondMFDeriv
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem core_second_tensor_overlap_mfderiv (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : secondDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
    let T := coreSecondTransition Q p q
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,w)
        (secondLocalActualProjectiveAHS Q D p y w v) =
      secondLocalActualProjectiveAHS Q D q (φ y)
        (secondMobius (G y) w)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,w) v) := by
  dsimp
  have heq := coreSecondTransition_eventuallyEq Q p q lift y hy hx w hden
  rw [heq.mfderiv_eq (I := 𝓘(ℝ, ℍ × ℂ))
    (I' := 𝓘(ℝ, ℍ × ℂ))]
  exact actual_second_tensor_overlap_mfderiv Q D p q lift
    y hy hx w hden v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreSecondTensor
