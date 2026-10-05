import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredAffinePoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTensorMFDeriv

/-! The global pointwise projective tensor, when the actual selected CP¹
chart is `[1:z]`, has the independently constructed local formula in every
refined adapted target chart whose transformed fiber remains in `[1:w]`.
The derivative is that of the literal projective bundle core transition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredZeroOverlap

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveCoreTransitionGerm
  FourDimensionalHalfSpinProjectiveCoreTensorMFDeriv
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
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

theorem preferred_zero_local_formula (z : SpinorBundleTotal Q)
    (hzero : preferredProjectiveChartIndex z.2 = 0)
    (v : TangentSpace (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)) z) :
    projectiveTangentModelEquiv (tangentComplex Q D z v) =
      localActualProjectiveAHS Q D z.1
        (extChartAt 𝓘(ℝ, ℍ) z.1 z.1)
        (preferredProjectiveScalar z.2)
        (projectiveTangentModelEquiv v) := by
  simp only [tangentComplex, preferredLocalModel, hzero,
    ↓reduceIte, LinearMap.comp_apply]
  exact projectiveTangentModelEquiv.apply_symm_apply _

theorem preferred_zero_arbitrary_base_formula (z : SpinorBundleTotal Q)
    (hzero : preferredProjectiveChartIndex z.2 = 0)
    (q : M) (lift : unitary ℍ)
    (hy : (extChartAt 𝓘(ℝ, ℍ) z.1 z.1) ∈
      chartOverlap (I := 𝓘(ℝ, ℍ)) z.1 q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) z.1).symm
        (extChartAt 𝓘(ℝ, ℍ) z.1 z.1) ∈
      liftNeighborhood Q (achart ℍ z.1) (achart ℍ q) lift)
    (hden : chartDen
      (halfSpinMatrix
        (scalarChart Q z.1 (achart ℍ z.1) (achart ℍ q) lift
          (extChartAt 𝓘(ℝ, ℍ) z.1 z.1)))
      (preferredProjectiveScalar z.2) ≠ 0)
    (v : TangentSpace (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)) z) :
    let y := extChartAt 𝓘(ℝ, ℍ) z.1 z.1
    let w := preferredProjectiveScalar z.2
    let r := scalarChart Q z.1 (achart ℍ z.1) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
        (coreAffineTransition Q z.1 q) (y,w)
        (projectiveTangentModelEquiv (tangentComplex Q D z v)) =
      localActualProjectiveAHS Q D q
        (chartTransition (I := 𝓘(ℝ, ℍ)) z.1 q y)
        (mobius (G y) w)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
          (coreAffineTransition Q z.1 q) (y,w)
          (projectiveTangentModelEquiv v)) := by
  dsimp
  rw [preferred_zero_local_formula Q D z hzero v]
  exact core_tensor_overlap_mfderiv Q D z.1 q lift
    (extChartAt 𝓘(ℝ, ℍ) z.1 z.1) hy hx
    (preferredProjectiveScalar z.2) hden
    (projectiveTangentModelEquiv v)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredZeroOverlap
