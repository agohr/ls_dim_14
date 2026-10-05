import QuaternionicSymmetry.ManifoldTwistorLocalContactProjectorOverlap

/-! Covariance of the smooth horizontal projector under derivatives of the
actual raw twistor sphere-bundle chart transitions. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

theorem rawTangentTransition_horizontalProjection
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) (u : E)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    rawTangentTransition Q p q
      (localHorizontalProjection Q D p
        ((y,u),⟨coefficientSphereHomeomorph a,v⟩)) =
      localHorizontalProjection Q D q
        (rawTangentTransition Q p q
          ((y,u),⟨coefficientSphereHomeomorph a,v⟩)) := by
  let uv : E × verticalSubmodule a := (u,sphereTangentVerticalEquiv a v)
  let H := localHorizontalPlaneProjection Q D p y hy.1 a uv
  let T := localTangentTransition Q D p q y hy a uv
  let b := rotatedCoefficient Q p q y hy a
  let yq := chartTransition (I := 𝓘(ℝ,E)) p q y
  have hq : yq ∈ (extChartAt 𝓘(ℝ,E) q).target :=
    (extChartAt 𝓘(ℝ,E) q).map_source hy.2
  have hHp : localHorizontalProjection Q D p
      ((y,u),⟨coefficientSphereHomeomorph a,v⟩) =
      ((y,H.1),⟨coefficientSphereHomeomorph a,
        (sphereTangentVerticalEquiv a).symm H.2⟩) := by
    simpa only [H, localHorizontalPlaneProjection_apply, uv,
      LinearEquiv.symm_apply_apply] using
      localHorizontalProjection_eq_horizontalLift Q D p y hy.1 a u v
  have hTH := rawTangentTransition_eq_local Q D p q y hy a
    H.1 ((sphereTangentVerticalEquiv a).symm H.2)
  have hT := rawTangentTransition_eq_local Q D p q y hy a u v
  have hcov := localTangentTransition_horizontalProjection Q D p q y hy a uv
  calc
    _ = rawTangentTransition Q p q
      ((y,H.1),⟨coefficientSphereHomeomorph a,
        (sphereTangentVerticalEquiv a).symm H.2⟩) := by rw [hHp]
    _ = ((yq,(localTangentTransition Q D p q y hy a H).1),
        ⟨coefficientSphereHomeomorph b,
          (sphereTangentVerticalEquiv b).symm
            (localTangentTransition Q D p q y hy a H).2⟩) := by
      simpa only [LinearEquiv.apply_symm_apply, yq, b] using hTH
    _ = ((yq,(localHorizontalPlaneProjection Q D q yq hq b T).1),
        ⟨coefficientSphereHomeomorph b,
          (sphereTangentVerticalEquiv b).symm
            (localHorizontalPlaneProjection Q D q yq hq b T).2⟩) := by
      rw [hcov]
    _ = localHorizontalProjection Q D q
      ((yq,T.1),⟨coefficientSphereHomeomorph b,
        (sphereTangentVerticalEquiv b).symm T.2⟩) := by
      have h := localHorizontalProjection_eq_horizontalLift Q D q yq hq b
        T.1 ((sphereTangentVerticalEquiv b).symm T.2)
      simpa only [localHorizontalPlaneProjection_apply,
        LinearEquiv.apply_symm_apply] using h.symm
    _ = _ := by rw [hT]

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
