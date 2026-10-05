import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaForm

/-! Exact cancellation between the derivative of the adapted tangent
gauge and the derivative of its inverse. This identifies the adapted
ordinary Levi-Civita form on actual soldered tangent vectors. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaSolder

open Filter Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicFrameGaugeInfinity
open ManifoldQuaternionicAdaptedLeviCivitaForm
open LocalConnectionGauge
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

theorem adaptedLeviCivitaForm_apply_solder (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    adaptedLeviCivitaForm Q g D p y u (solder Q p y v) =
      solder Q p y (D.form p y u v) -
        fderiv ℝ (solder Q p) y u v := by
  have hleft : (fun z => solder Q p z * coordinateInverse Q p z) =ᶠ[𝓝 y]
      fun _ => 1 := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateInverse_right Q p z hz
  have hright : coordinateInverse Q p y * solder Q p y = 1 :=
    coordinateInverse_left Q p y hy
  have hg : DifferentiableAt ℝ (coordinateInverse Q p) y :=
    (coordinateInverse_contDiffAt_infinity Q p y hy).differentiableAt (by simp)
  have hh : DifferentiableAt ℝ (solder Q p) y :=
    (solder_contDiffAt_infinity Q p y hy).differentiableAt (by simp)
  have hder := fderiv_inverse_pair (coordinateInverse Q p) (solder Q p)
    y hg hh hleft hright u
  have hderv := congrArg (fun T : E →L[ℝ] E => T v) hder
  have hcancel : solder Q p y
      ((fderiv ℝ (coordinateInverse Q p) y u) (solder Q p y v)) =
        -(fderiv ℝ (solder Q p) y u v) := by
    have hderv' : -(solder Q p y
        ((fderiv ℝ (coordinateInverse Q p) y u) (solder Q p y v))) =
          fderiv ℝ (solder Q p) y u v := by
      simpa only [ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.neg_apply] using hderv.symm
    calc
      _ = -(-solder Q p y
          ((fderiv ℝ (coordinateInverse Q p) y u) (solder Q p y v))) := by simp
      _ = _ := by rw [hderv']
  have hraw : coordinateInverse Q p y (solder Q p y v) = v := by
    have h := congrArg (fun T : E →L[ℝ] E => T v) hright
    simpa only [ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply] using h
  rw [adaptedLeviCivitaForm, transform_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    map_add, hraw, hcancel, neg_smul, one_smul]
  abel

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaSolder
