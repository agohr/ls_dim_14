import QuaternionicSymmetry.SelectedTorusLieSpanDerivativeRange
import QuaternionicSymmetry.GlobalSmoothTangentCurve

/-! The intrinsic smooth-curve Lie span of the SAME selected torus is
exactly the differential range of its actual BG-L3 smooth embedding. -/

namespace QuaternionicSymmetry.SelectedTorusLieSpanDerivativeEquality

open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open SelectedTorusEmbeddedLieAtlas SelectedTorusLieSpanDerivativeRange
open GlobalSmoothTangentCurve
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ} (T : TorusEmbedding G r)
  (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)

theorem derivative_range_le_torusLieSpan :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    LinearMap.range
        ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1).toLinearMap) ≤
      torusLieSpan (V := V) T := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  rintro v ⟨w, rfl⟩
  obtain ⟨c, hc0, hcSmooth, hcVelocity⟩ :=
    exists_global_smooth_curve_with_velocity (E := Fin d → ℝ)
      (M := Fin r → Circle) (1 : Fin r → Circle) w
  let f : ℝ → G := T.hom ∘ c
  have hf0 : f 0 = 1 := by simp [f, hc0]
  have hfRange : ∀ s : ℝ, f s ∈ T.hom.range := by
    intro s
    exact ⟨c s, rfl⟩
  have hfSmooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,V) ∞ f :=
    (selected_hom_smooth T g).comp hcSmooth
  have hcomp := mfderiv_comp (I := 𝓘(ℝ,ℝ))
    (I' := 𝓘(ℝ,Fin d → ℝ)) (I'' := 𝓘(ℝ,V)) (x := (0 : ℝ))
    ((selected_hom_smooth T g).mdifferentiable (by simp) (c 0))
    (hcSmooth.mdifferentiable (by simp) 0)
  rw [hc0] at hcomp
  have hfVelocity : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,V) f 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1 w := by
    have h := congrArg
      (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ,V) (f 0) => L (1 : ℝ)) hcomp
    change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,V) f 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1
        (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ) c 0 (1 : ℝ)) at h
    simpa only [hcVelocity] using h
  apply Submodule.subset_span
  exact ⟨f, hf0, hfRange, hfSmooth, hfVelocity⟩

theorem torusLieSpan_eq_derivative_range
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    torusLieSpan (V := V) T =
      LinearMap.range
        ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1).toLinearMap) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  exact le_antisymm
    (torusLieSpan_le_derivative_range T g hImm hLee)
    (derivative_range_le_torusLieSpan T g)

end
end QuaternionicSymmetry.SelectedTorusLieSpanDerivativeEquality
