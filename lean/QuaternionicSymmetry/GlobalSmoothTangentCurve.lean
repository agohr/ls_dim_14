import QuaternionicSymmetry.BoundedSmoothCurveGerm
import QuaternionicSymmetry.GeneralImmersionChartDerivativeRange

/-! A prescribed tangent vector at any point of a finite-dimensional real
manifold is the velocity of a globally defined smooth curve. The coordinate
line is compressed by a bounded smooth parameter before applying the chart. -/

namespace QuaternionicSymmetry.GlobalSmoothTangentCurve

open Manifold Filter Metric
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_global_smooth_curve_with_velocity
    (x : M) (v : TangentSpace 𝓘(ℝ,E) x) :
    ∃ c : ℝ → M,
      c 0 = x ∧
      ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ c ∧
      mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) c 0 (1 : ℝ) = v := by
  let σ := extChartAt 𝓘(ℝ,E) x
  let y : E := σ x
  have hy : y ∈ σ.target := mem_extChartAt_target x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target x) y hy
  let u : E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) σ x v
  have hδ : 0 < ε / (‖u‖ + 1) := by positivity
  obtain ⟨φ, hφ, hφgerm, hφbound⟩ :=
    BoundedSmoothCurveGerm.exists_bounded_identity_germ
      (ε / (‖u‖ + 1)) hδ
  let line : ℝ → E := fun t => y + φ t • u
  have hlineSmooth : ContDiff ℝ ∞ line :=
    contDiff_const.add (hφ.smul_const u)
  have hlineTarget : ∀ t, line t ∈ σ.target := by
    intro t
    apply hball
    have hnorm : ‖φ t • u‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs]
      have hnu : 0 ≤ ‖u‖ := norm_nonneg u
      calc
        |φ t| * ‖u‖ ≤ |φ t| * (‖u‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ < (ε / (‖u‖ + 1)) * (‖u‖ + 1) :=
          mul_lt_mul_of_pos_right (hφbound t) (by positivity)
        _ = ε := by field_simp
    simpa [line, dist_eq_norm] using hnorm
  let c : ℝ → M := fun t => σ.symm (line t)
  have hφ0 : φ 0 = 0 := by
    simpa using hφgerm.eq_of_nhds
  have hline0 : line 0 = y := by simp [line, hφ0]
  have hc0 : c 0 = x := by
    simp only [c, hline0]
    exact (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)
  have hcSmooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ c := by
    have hsymm : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ σ.symm σ.target :=
      contMDiffOn_extChartAt_symm x
    exact contMDiffOn_univ.mp
      (hsymm.comp hlineSmooth.contMDiff.contMDiffOn
        (fun t _ => hlineTarget t))
  refine ⟨c, hc0, hcSmooth, ?_⟩
  have hlineGerm : line =ᶠ[𝓝 (0 : ℝ)] fun t => y + t • u := by
    filter_upwards [hφgerm] with t ht
    simp [line, ht]
  have hlineDeriv : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) line 0 (1 : ℝ) = u := by
    rw [mfderiv_eq_fderiv]
    rw [hlineGerm.fderiv_eq]
    have hfd : HasFDerivAt (fun t : ℝ => y + t • u)
        ((ContinuousLinearMap.id ℝ ℝ).smulRight u) 0 := by
      convert
        (hasFDerivAt_const (𝕜 := ℝ) y (0 : ℝ)).add
          ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const u)
        using 1 <;> ext t <;> simp
    rw [hfd.fderiv]
    change (1 : ℝ) • u = u
    simp
  have hσ : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) σ.symm y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x y hy).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hy)).mdifferentiableAt (by simp)
  have hσ' : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) σ.symm (line 0) := by
    simpa [hline0] using hσ
  have hchain := mfderiv_comp (I := 𝓘(ℝ,ℝ))
    (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E)) (x := (0 : ℝ))
    hσ' (hlineSmooth.contMDiff.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) c 0 = _ at hchain
  rw [hline0] at hchain
  have hright := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    (I := 𝓘(ℝ,E)) (x := x) hy
  have hxy : σ.symm y = x :=
    (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)
  rw [hxy] at hright
  have hσeq : mfderivWithin 𝓘(ℝ,E) 𝓘(ℝ,E) σ.symm
      (Set.range 𝓘(ℝ,E)) y = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) σ.symm y := by
    rw [show Set.range 𝓘(ℝ,E) = Set.univ by simp, mfderivWithin_univ]
  rw [hσeq] at hright
  have hv := congrArg
    (fun L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x => L v)
    hright
  have hcurve := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ,E) x => L 1) hchain
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) c 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) σ.symm y
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) line 0 (1 : ℝ)) at hcurve
  rw [hlineDeriv] at hcurve
  calc
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) c 0 (1 : ℝ) =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) σ.symm y u := hcurve
    _ = v := by simpa only [u, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hv

end
end QuaternionicSymmetry.GlobalSmoothTangentCurve
