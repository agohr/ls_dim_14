import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaForm
import QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature
import QuaternionicSymmetry.ManifoldQuaternionicFrameGaugeInfinity
import QuaternionicSymmetry.LocalConnectionGauge

/-! Curvature of the actual adapted Levi-Civita gauge is exactly the
coordinate Levi-Civita curvature conjugated by the genuine solder frame.
No curvature or quaternionic-preservation assumption enters this bridge. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCurvatureBridge

open Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicFrameGaugeInfinity
open LocalConnectionGauge
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

theorem adaptedLeviCivita_curvature_eq_solder_coordinate
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v w : E) :
    LocalConnection.curvature (adaptedLeviCivitaForm Q g D p) y u v w =
      solder Q p y
        (LocalConnection.curvature (D.form p) y u v
          (coordinateInverse Q p y w)) := by
  have hΓ : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)).differentiableAt
        (by simp)
  have hg : ContDiffAt ℝ 2 (coordinateInverse Q p) y :=
    (coordinateInverse_contDiffAt_infinity Q p y hy).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  have hh : DifferentiableAt ℝ (solder Q p) y :=
    (solder_contDiffAt_infinity Q p y hy).differentiableAt (by simp)
  have hleft : (fun z => solder Q p z * coordinateInverse Q p z) =ᶠ[𝓝 y]
      fun _ => 1 := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateInverse_right Q p z hz
  have hright : coordinateInverse Q p y * solder Q p y = 1 :=
    coordinateInverse_left Q p y hy
  have h := curvature_transform (D.form p) (coordinateInverse Q p)
    (solder Q p) y hΓ hg hh hleft hright u v
  have hw := congrArg (fun A : E →L[ℝ] E => A w) h
  simpa only [adaptedLeviCivitaForm, ContinuousLinearMap.mul_apply] using hw

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCurvatureBridge
