import QuaternionicSymmetry.ManifoldQuaternionicTwistorSplitMetric

/-! Bundle the positive split metric as a genuine bounded bilinear form on
each actual twistor tangent fiber. Smooth variation is a separate step. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBilinear

open ManifoldQuaternionicTwistorSplitMetric
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

private noncomputable instance (z : SphereBundleTotal Q) :
    FiniteDimensional ℝ (TangentSpace (J (E := E)) z) :=
  FiniteDimensional.of_injective (preferredTangentEquiv Q z).toLinearMap
    (preferredTangentEquiv Q z).injective

private def splitMetricLinearRight (z : SphereBundleTotal Q)
    (u : TangentSpace (J (E := E)) z) :
    TangentSpace (J (E := E)) z →ₗ[ℝ] ℝ where
  toFun := splitMetric Q D z u
  map_add' := splitMetric_add_right Q D z u
  map_smul' := by
    intro c v
    exact (splitMetric_smul_right Q D z c u v).trans (smul_eq_mul c _).symm

private def splitMetricLinearLeft (z : SphereBundleTotal Q) :
    TangentSpace (J (E := E)) z →ₗ[ℝ]
      (TangentSpace (J (E := E)) z →L[ℝ] ℝ) where
  toFun u := (splitMetricLinearRight Q D z u).toContinuousLinearMap
  map_add' := by
    intro u v
    ext w
    change splitMetric Q D z (u + v) w =
      splitMetric Q D z u w + splitMetric Q D z v w
    rw [splitMetric_symm Q D z (u + v) w,
      splitMetric_add_right, splitMetric_symm Q D z w u,
      splitMetric_symm Q D z w v]
  map_smul' := by
    intro c u
    ext w
    change splitMetric Q D z (c • u) w = c • splitMetric Q D z u w
    rw [splitMetric_symm Q D z (c • u) w,
      splitMetric_smul_right, splitMetric_symm Q D z w u]
    exact (smul_eq_mul c _).symm

/-- The actual split metric as a continuous bilinear form on each tangent
fiber, without replacing the pointwise geometry by an abstract form. -/
def splitMetricCLM (z : SphereBundleTotal Q) :
    TangentSpace (J (E := E)) z →L[ℝ]
      TangentSpace (J (E := E)) z →L[ℝ] ℝ :=
  (splitMetricLinearLeft Q D z).toContinuousLinearMap

theorem splitMetricCLM_apply (z : SphereBundleTotal Q)
    (u v : TangentSpace (J (E := E)) z) :
    splitMetricCLM Q D z u v = splitMetric Q D z u v := rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBilinear
