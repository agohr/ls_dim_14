import QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricity
import QuaternionicSymmetry.ManifoldQuaternionicKSWEinsteinAdapted
import QuaternionicSymmetry.ManifoldQuaternionicFirstBianchi

/-! Ricci and Einstein equations in the genuine chart-coordinate tangent
connection. The Ricci trace is basis independent; the chart metric is the
solder pullback of the adapted orthonormal metric. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCoordinateEinstein
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWEinsteinAdapted
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open QuaternionicSymmetry.LocalConnectionGauge
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def coordinateRicciEndomorphism (p : M) (y v w : E) : E →ₗ[ℝ] E where
  toFun u := LocalConnection.curvature (coordinateConnection Q D p) y u v w
  map_add' := by intros; simp
  map_smul' := by intros; simp

def coordinateRicci (p : M) (y v w : E) : ℝ :=
  LinearMap.trace ℝ E (coordinateRicciEndomorphism Q D p y v w)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem coordinate_curvature_conj (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w : E) :
    LocalConnection.curvature (coordinateConnection Q D p) y u v w =
      (solderEquiv Q p y hy).symm
        (D.curvature Q p y u v (solderEquiv Q p y hy w)) := by
  have hΓ : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  have hg := ManifoldQuaternionicCoordinateSecondBianchi.solder_contDiffAt Q p y hy
  have hh := ManifoldQuaternionicCoordinateSecondBianchi.coordinateInverse_contDiffAt Q p y hy
  have hleft : (fun z => coordinateInverse Q p z * solder Q p z) =ᶠ[𝓝 y]
      fun _ => 1 := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateInverse_left Q p z hz
  have hF := curvature_transform (D.form p) (solder Q p) (coordinateInverse Q p)
    y hΓ (hg.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num))
      (hh.differentiableAt (by norm_num)) hleft
        (coordinateInverse_right Q p y hy) u v
  have h := congrArg (fun F : E →L[ℝ] E => F w) hF
  simpa only [coordinateConnection, CompatibleTangentConnection.curvature,
    ContinuousLinearMap.mul_apply, solderEquiv,
    unsolder_eq_fromFrame Q p y hy, coordinateInverse] using h

omit [Nontrivial E] in
theorem coordinateRicci_eq_adapted (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    coordinateRicci Q D p y v w =
      localRicci Q D p y hy (solder Q p y v) (solder Q p y w) := by
  let e := solderEquiv Q p y hy
  have he : coordinateRicciEndomorphism Q D p y v w =
      e.symm.toLinearEquiv.conj
        (ricciEndomorphism Q D p y hy (e v) (e w)) := by
    ext u
    change LocalConnection.curvature (coordinateConnection Q D p) y u v w = _
    rw [coordinate_curvature_conj Q D p y hy]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ricciEndomorphism]
    change e.symm (D.curvature Q p y u v (e w)) =
      e.symm (D.curvature Q p y (e.symm (e u)) (e.symm (e v)) (e w))
    rw [e.symm_apply_apply, e.symm_apply_apply]
  rw [coordinateRicci, he, LinearMap.trace_conj']
  simpa only [e, solderEquiv] using
    (localRicci_eq_trace Q D p y hy (e v) (e w)).symm

theorem coordinateRicci_einstein
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    coordinateRicci Q D p y v w =
      (scalarRatio S Q D p y hy *
        ((Module.finrank ℝ E : ℝ) + 8)) * coordinateMetric Q p y v w := by
  rw [coordinateRicci_eq_adapted Q D p y hy,
    localRicci_einstein S Q D hdecomp p y hy]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicCoordinateEinstein
