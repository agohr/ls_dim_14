import QuaternionicSymmetry.ManifoldQuaternionicRiemannianDistance
import QuaternionicSymmetry.ManifoldQuaternionicFundamentalSymmetry

/-! Differential metric preservation implies preservation of the actual
Riemannian path distance. This is the bridge from the smooth symmetry group
to metric-space isometries; no auxiliary distance is substituted. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicMetricIsometryDistance

open Bundle Manifold ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicFundamentalSymmetry
open scoped Manifold ContDiff Bundle ENNReal
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem mfderiv_enorm_eq
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (hf : PreservesMetric Q f) (x : M) (v : TangentSpace 𝓘(ℝ,E) x) :
    letI := actualRiemannianBundle Q
    ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v‖ₑ = ‖v‖ₑ := by
  letI := actualRiemannianBundle Q
  have hi := hf x v v
  change inner ℝ (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v) = inner ℝ v v at hi
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  have hn : ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v‖ = ‖v‖ := by
    nlinarith [norm_nonneg v,
      norm_nonneg (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f : M → M) x v)]
  exact enorm_eq_iff_norm_eq.mpr hn

theorem riemannianEDistance_map_le
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (hf : PreservesMetric Q f) (x y : M) :
    riemannianEDistance Q (f x) (f y) ≤ riemannianEDistance Q x y := by
  letI := actualRiemannianBundle Q
  change riemannianEDist 𝓘(ℝ,E) (f x) (f y) ≤ riemannianEDist 𝓘(ℝ,E) x y
  rw [riemannianEDist, riemannianEDist]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let η : Path (f x) (f y) := γ.map f.continuous
  have hη : ContMDiff (𝓡∂ 1) 𝓘(ℝ,E) 1 η :=
    (f.contMDiff.of_le (by simp)).comp hγ
  refine (iInf_le_of_le η (iInf_le_of_le hη le_rfl)).trans_eq ?_
  apply MeasureTheory.lintegral_congr
  intro t
  change ‖mfderiv (𝓡∂ 1) 𝓘(ℝ,E) ((f : M → M) ∘ γ) t 1‖ₑ = _
  rw [mfderiv_comp t (f.contMDiff.mdifferentiable (by simp) (γ t))
    (hγ.mdifferentiable (by decide) t)]
  exact mfderiv_enorm_eq Q f hf (γ t) _

theorem riemannianEDistance_map
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (hf : PreservesMetric Q f) (x y : M) :
    riemannianEDistance Q (f x) (f y) = riemannianEDistance Q x y := by
  apply le_antisymm (riemannianEDistance_map_le Q f hf x y)
  simpa only [Diffeomorph.symm_apply_apply] using
    riemannianEDistance_map_le Q f.symm (metric_symm Q hf) (f x) (f y)

/-- The actual smooth metric symmetry is an isometry equivalence for the
genuine Riemannian metric-space structure. -/
def metricIsometryEquiv [T3Space M] [PreconnectedSpace M]
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) (hf : PreservesMetric Q f) :
    letI := riemannianMetricSpace Q
    M ≃ᵢ M := by
  letI := riemannianMetricSpace Q
  exact { f.toEquiv with
    isometry_toFun := fun x y => riemannianEDistance_map Q f hf x y }

end
end QuaternionicSymmetry.ManifoldQuaternionicMetricIsometryDistance
