import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllCoreChartDomain
import QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors

/-! On a genuine refined adapted overlap, membership of the transformed
projective point in the target affine chart supplies exactly the matrix
denominator needed by all four literal-core derivative identities. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualChartDomain

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinSmoothLocalFactors
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinActualTransitionSmooth
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

theorem actual_denominator_ne_zero_of_target_mem
    (i j : Fin 2) (p q : M) (lift : unitary ℍ)
    (y : ℍ)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hmem : spinorTransition Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
        (indexedSourcePoint i z) ∈ affineDomain 1 j) :
    indexedDenominator i j
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0 := by
  obtain ⟨a, b, ha, _, _, hproj, _⟩ :=
    local_factors_clifford Q (achart ℍ p) (achart ℍ q) lift
      ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx
  have hmem' : projectiveHalfSpin a (indexedSourcePoint i z) ∈
      affineDomain 1 j := by
    rw [← hproj]
    exact hmem
  have hd := indexedDenominator_ne_zero_of_target_mem i j a z hmem'
  simpa only [ha] using hd

theorem core_denominator_ne_zero_of_target_mem
    (i j : Fin 2) (p q : M) (lift : unitary ℍ)
    (y : ℍ)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hmem : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y,
          indexedSourcePoint i z) ∈ affineDomain 1 j) :
    indexedDenominator i j
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0 := by
  have hcore : spinorCoordChange Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y, indexedSourcePoint i z) =
      spinorTransition Q (achart ℍ p) (achart ℍ q)
        ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hx.1.1 hx.1.2
        (indexedSourcePoint i z) := by
    dsimp [spinorCoordChange]
    rw [dif_pos ⟨hx.1.1, hx.1.2⟩]
  exact actual_denominator_ne_zero_of_target_mem Q i j p q lift y hx z
    (by simpa only [hcore] using hmem)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualChartDomain
