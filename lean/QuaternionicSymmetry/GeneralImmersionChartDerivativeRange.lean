import QuaternionicSymmetry.GeneralImmersionChartPullbackMetric

/-! In a genuine self-model chart, every manifold differential vector
is the derivative of the chartwise map in an explicit chart direction. -/

namespace QuaternionicSymmetry.GeneralImmersionChartDerivativeRange

open Manifold
open scoped Manifold ContDiff Topology
noncomputable section

variable {E V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chart_derivative_covers_manifold_differential
    (f : M → V) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (w : TangentSpace 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm y)) :
    ∃ u : E,
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) p).symm) y u =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f
          ((extChartAt 𝓘(ℝ,E) p).symm y) w := by
  let σ := (extChartAt 𝓘(ℝ,E) p).symm
  let x := σ y
  let u := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p) x w
  refine ⟨u, ?_⟩
  have hσ : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) σ y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)).mdifferentiableAt (by simp)
  have hright := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    (I := 𝓘(ℝ,E)) (x := p) hy
  have hσeq : mfderivWithin 𝓘(ℝ,E) 𝓘(ℝ,E) σ (Set.range 𝓘(ℝ,E)) y =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) σ y := by
    rw [show Set.range 𝓘(ℝ,E) = Set.univ by simp, mfderivWithin_univ]
  rw [hσeq] at hright
  have hw := congrArg (fun L : TangentSpace 𝓘(ℝ,E) x →L[ℝ]
      TangentSpace 𝓘(ℝ,E) x => L w) hright
  have hcomp := mfderiv_comp y (hf.mdifferentiableAt (by simp)) hσ
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) (f ∘ σ) y = _ at hcomp
  rw [mfderiv_eq_fderiv] at hcomp
  rw [hcomp]
  change (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x)
    ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) σ y) u) = _
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrArg (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x) hw

end
end QuaternionicSymmetry.GeneralImmersionChartDerivativeRange
