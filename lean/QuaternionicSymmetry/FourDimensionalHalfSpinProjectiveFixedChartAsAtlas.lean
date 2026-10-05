import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPole
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartInverse

/-! Every fixed base/CP¹ affine chart is literally the genuine independent
projective-bundle atlas chart centered at the corresponding coordinate pole,
after the checked one-complex-coordinate real-linear equivalence. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartAsAtlas

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartPole
  FourDimensionalHalfSpinProjectivePreferredFixedChart
  FourDimensionalHalfSpinProjectivePreferredFixedChartInverse
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem fixedChart_eq_poleAtlas (p : M) (i : Fin 2)
    (w : SpinorBundleTotal Q) :
    fixedProjectiveChart Q p i w =
      projectiveTangentModelEquiv
        ((extChartAt productModel (chartPole Q p i)) w) := by
  simpa only [chartPole_base, chartPole_preferredIndex] using
    preferred_fixedChart_eq_extChartAt Q (chartPole Q p i) w

theorem fixedChartInv_eq_poleAtlas (p : M) (i : Fin 2)
    (yw : ℍ × ℂ) :
    fixedProjectiveChartInv Q p i yw =
      (extChartAt productModel (chartPole Q p i)).symm
        (projectiveTangentModelEquiv.symm yw) := by
  simpa only [chartPole_base, chartPole_preferredIndex] using
    preferred_fixedChartInv_eq_extChartAt_symm Q (chartPole Q p i) yw

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartAsAtlas
