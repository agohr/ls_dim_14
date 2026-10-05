import QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexInfinity

/-! Package the proven action and its real/complex smoothness as honest
twistor diffeomorphisms, rather than bare endomaps. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryDiffeomorph

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorLiftSmooth
open ManifoldQuaternionicIsometryComplexInfinity
open ManifoldTwistorSphereCore
open ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Every quaternionic base isometry induces a genuine smooth real
diffeomorphism of the associated twistor sphere bundle. -/
def realLift (f : QuaternionicIsometries Q) :
    Diffeomorph ((𝓘(ℝ,E)).prod (𝓡 2)) ((𝓘(ℝ,E)).prod (𝓡 2))
      (SphereBundleTotal Q) (SphereBundleTotal Q) ∞ where
  toEquiv := MulAction.toPerm f
  contMDiff_toFun := by
    change ContMDiff ((𝓘(ℝ,E)).prod (𝓡 2)) ((𝓘(ℝ,E)).prod (𝓡 2))
      ∞ (sphereTotalMap Q f)
    exact sphereTotalMap_contMDiff Q f
  contMDiff_invFun := by
    change ContMDiff ((𝓘(ℝ,E)).prod (𝓡 2)) ((𝓘(ℝ,E)).prod (𝓡 2))
      ∞ (sphereTotalMap Q f⁻¹)
    exact sphereTotalMap_contMDiff Q f⁻¹

theorem realLift_apply (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) : realLift Q f z = sphereTotalMap Q f z := rfl

/-- The same underlying diffeomorphism is biholomorphic in every compatible
complex twistor atlas. -/
def complexLift (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    Diffeomorph 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal Q) (SphereBundleTotal Q) ∞ := by
  letI := B.charts
  letI := B.realManifold
  letI := B.complexManifold
  exact {
    toEquiv := MulAction.toPerm f
    contMDiff_toFun := sphereTotalMap_contMDiff_complex_infty Q D B f
    contMDiff_invFun := sphereTotalMap_contMDiff_complex_infty Q D B f⁻¹ }

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryDiffeomorph
