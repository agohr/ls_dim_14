import QuaternionicSymmetry.ManifoldQuaternionicInducedSplitDerivative
import QuaternionicSymmetry.ManifoldQuaternionicIsometryBaseComplex

/-! Quaternionic base-complex intertwining for the actual rectangular
immersive derivative, at every induced twistor point. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedBaseComplex
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedSplitDerivative
open ManifoldQuaternionicIsometryBaseComplex
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLocalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

theorem tangentSynth_eq_chartBaseComplex
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,F)) (M := N) (n := ∞))
    (c : N) (a : coefficientSphere) :
    tangentSynth Q c a.1 =
      chartBaseComplex Q c (extChartAt 𝓘(ℝ,F) c c) a := by
  rw [chartBaseComplex_center Q c a]
  rfl

theorem induced_mfderiv_intertwines_chartBaseComplex
    (z : ManifoldTwistorSphereCore.SphereBundleTotal R.tangent)
    (v : F) :
    let a := coefficientSphereHomeomorph.symm z.2
    let b := coefficientSphereHomeomorph.symm
      (sphereTotalMap P R ι hι hR z).2
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1
      (chartBaseComplex R.tangent z.1
        (extChartAt 𝓘(ℝ,F) z.1 z.1) a v) =
      chartBaseComplex P.tangent (sphereTotalMap P R ι hι hR z).1
        (extChartAt 𝓘(ℝ,E) (sphereTotalMap P R ι hι hR z).1
          (sphereTotalMap P R ι hι hR z).1) b
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1 v) := by
  dsimp only
  rw [sphereTotalMap_base P R ι hι hR z,
    ← tangentSynth_eq_chartBaseComplex R.tangent z.1,
    ← tangentSynth_eq_chartBaseComplex P.tangent (ι z.1)]
  have hcoeff := sphereTotalMap_center_coefficients P R ι hι hR z
  change (coefficientSphereHomeomorph.symm
    (sphereTotalMap P R ι hι hR z).2).1 =
      coefficientMap P R ι hι hR z.1
        (coefficientSphereHomeomorph.symm z.2).1 at hcoeff
  rw [hcoeff]
  exact coefficientMap_intertwines P R ι hι hR z.1 _ v

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedBaseComplex
