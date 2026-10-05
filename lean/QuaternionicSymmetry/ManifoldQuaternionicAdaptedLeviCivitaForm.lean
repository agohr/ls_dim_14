import QuaternionicSymmetry.ManifoldQuaternionicFrameGaugeInfinity
import QuaternionicSymmetry.GeneralLeviCivitaSource
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Transport an ordinary coordinate Levi-Civita form through the actual
orthonormal tangent gauge. The resulting adapted form is smooth to all
orders on every valid preferred chart. Remaining connection laws are
proved separately rather than assumed. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaForm

open Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicFrameGaugeInfinity
open LocalConnectionGauge
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

def adaptedLeviCivitaForm (p : M) :
    LocalConnection.Form (E := E) (A := E →L[ℝ] E) :=
  LocalConnectionGauge.transform (D.form p)
    (coordinateInverse Q p) (solder Q p)

theorem adaptedLeviCivitaForm_smooth (p : M) :
    ContDiffOn ℝ ∞ (adaptedLeviCivitaForm Q g D p)
      (extChartAt 𝓘(ℝ,E) p).target := by
  apply contDiffOn_clm_apply.mpr
  intro v y hy
  have hΓ : ContDiffAt ℝ ∞ (D.form p) y :=
    (D.smooth_form p).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  have hg : ContDiffAt ℝ ∞ (coordinateInverse Q p) y :=
    coordinateInverse_contDiffAt_infinity Q p y hy
  have hh : ContDiffAt ℝ ∞ (solder Q p) y :=
    solder_contDiffAt_infinity Q p y hy
  have hdg : ContDiffAt ℝ ∞ (fderiv ℝ (coordinateInverse Q p)) y :=
    hg.fderiv_right (m := ∞) (by simp)
  have hΓv : ContDiffAt ℝ ∞ (fun z => D.form p z v) y :=
    hΓ.clm_apply contDiffAt_const
  have hdgv : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (coordinateInverse Q p) z v) y :=
    hdg.clm_apply contDiffAt_const
  have hmain : ContDiffAt ℝ ∞
      (fun z => solder Q p z *
        (D.form p z v * coordinateInverse Q p z +
          fderiv ℝ (coordinateInverse Q p) z v)) y :=
    hh.mul ((hΓv.mul hg).add hdgv)
  have heq : (fun z => adaptedLeviCivitaForm Q g D p z v) =
      (fun z => solder Q p z *
        (D.form p z v * coordinateInverse Q p z +
          fderiv ℝ (coordinateInverse Q p) z v)) := by
    funext z
    rfl
  rw [heq]
  exact hmain.contDiffWithinAt

theorem adaptedLeviCivitaForm_contDiffAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ContDiffAt ℝ ∞ (adaptedLeviCivitaForm Q g D p) y :=
  (adaptedLeviCivitaForm_smooth Q g D p).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaForm
