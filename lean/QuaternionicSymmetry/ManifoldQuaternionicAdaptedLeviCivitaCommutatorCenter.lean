import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaOverlap
import QuaternionicSymmetry.GeneralAdaptedGaugeAdjointCovariance
import QuaternionicSymmetry.ManifoldQuaternionicChartPlaneDeconjugation
import QuaternionicSymmetry.GeneralLeviCivitaReflectedPlaneParallel
import QuaternionicSymmetry.ManifoldQuaternionicLocalGeneratorField

/-! Ordinary Q-parallelism of each genuine chart generator at a preferred
chart center implies the fixed adapted quaternionic commutator condition
for the concrete gauge-transported Levi-Civita form there. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCommutatorCenter

open Filter Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicFrameGaugeInfinity
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicChartProjection
open ManifoldQuaternionicChartPlaneDeconjugation
open ManifoldQuaternionicLocalGeneratorField
open ManifoldQuaternionicAdjointOverlap
open GeneralAdaptedGaugeAdjointCovariance
open GeneralLeviCivitaReflectedPlaneParallel
open VectorBundleFrameTransitions
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

theorem adaptedLeviCivitaForm_commutator_center
    (p : M) (t : Fin 3) (u : E)
    (hraw : covariantEndomorphismMap
        (D.form p (extChartAt 𝓘(ℝ,E) p p))
        (localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent p t)
        (extChartAt 𝓘(ℝ,E) p p) u ∈
          Q.chartSpan (achart E p) p) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    let J := quaternionicGenerator (Q.reduction.Q (achart E p)) t
    (adaptedLeviCivitaForm Q g D p y₀ u).comp J -
      J.comp (adaptedLeviCivitaForm Q g D p y₀ u) ∈
        quaternionicSpan (Q.reduction.Q (achart E p)) := by
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let i := achart E p
  let J := quaternionicGenerator (Q.reduction.Q i) t
  let G := coordinateInverse Q p
  let H := solder Q p
  let S := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent p t
  let Λ := D.form p y₀ u
  let dg := fderiv ℝ G y₀ u
  let dh := fderiv ℝ H y₀ u
  let Γ := adaptedLeviCivitaForm Q g D p y₀ u
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hp : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hbase : p ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i :=
    (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at p
  have hgh : G y₀ * H y₀ = 1 := coordinateInverse_left Q p y₀ hy
  have hhg : H y₀ * G y₀ = 1 := coordinateInverse_right Q p y₀ hy
  have hG : DifferentiableAt ℝ G y₀ :=
    (coordinateInverse_contDiffAt_infinity Q p y₀ hy).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ H y₀ :=
    (solder_contDiffAt_infinity Q p y₀ hy).differentiableAt (by simp)
  have hdh : dh = -(H y₀ * dg * H y₀) := by
    apply LocalConnectionGauge.fderiv_inverse_pair G H y₀ hG hH
    · filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
        with z hz
      exact coordinateInverse_right Q p z hz
    · exact hgh
  have hΓ : Γ = H y₀ * (Λ * G y₀ + dg) := rfl
  have hSval : S y₀ = G y₀ * J * H y₀ := by
    ext v
    simp only [S, localChartGeneratorField, hp, G, coordinateInverse,
      H, solder_eq_toFrame Q p y₀ hy,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
    rfl
  have hSlocal : S =ᶠ[𝓝 y₀] fun z => G z * J * H z := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    ext v
    simp only [S, localChartGeneratorField, G, coordinateInverse,
      H, solder_eq_toFrame Q p z hz,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
    rfl
  have hSderiv : fderiv ℝ S y₀ u = dg * J * H y₀ + G y₀ * J * dh := by
    rw [hSlocal.fderiv_eq]
    exact fderiv_conjugate_const G H J y₀ u hG hH
  have hidentity : G y₀ * (Γ * J - J * Γ) * H y₀ =
      covariantEndomorphismMap (D.form p y₀) S y₀ u := by
    rw [affine_adjoint_identity (G y₀) (H y₀) Λ dg Γ J dh
      hgh hΓ hdh]
    rw [covariantEndomorphismMap, hSval, hSderiv]
    ext v
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      neg_one_smul]
    abel
  have hdeconj : inverseChartConjugation Q i p
      (covariantEndomorphismMap (D.form p y₀) S y₀ u) ∈
        quaternionicSpan (Q.reduction.Q i) :=
    inverseChartConjugation_mem_quaternionicSpan Q i p hbase _ hraw
  have hback : inverseChartConjugation Q i p
      (covariantEndomorphismMap (D.form p y₀) S y₀ u) = Γ * J - J * Γ := by
    rw [inverseChartConjugation_apply, ← hidentity]
    have hHval : H y₀ = Q.frames.toFrame i p := by
      change solder Q p y₀ = _
      rw [solder_eq_toFrame Q p y₀ hy, hp]
    have hGval : G y₀ = Q.frames.fromFrame i p := by
      change coordinateInverse Q p y₀ = _
      simp only [coordinateInverse, hp]
      rfl
    rw [← hHval, ← hGval]
    change H y₀ * (G y₀ * (Γ * J - J * Γ) * H y₀) * G y₀ = _
    simp only [mul_assoc, ← mul_assoc (H y₀) (G y₀), hhg, one_mul,
      ← mul_assoc (Γ * J - J * Γ) (H y₀), hgh, mul_one]
  rw [hback] at hdeconj
  change (Γ.comp J - J.comp Γ) ∈ quaternionicSpan (Q.reduction.Q i)
  convert hdeconj using 1

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCommutatorCenter
