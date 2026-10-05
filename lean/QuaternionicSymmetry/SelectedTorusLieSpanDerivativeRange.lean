import QuaternionicSymmetry.SelectedTorusSmoothCurveLift
import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource

/-! The intrinsic Lie span of the SAME selected torus lies in the
derivative range of its actual smooth closed embedding. Each generating
curve lifts smoothly through the embedding by BG-D3. -/

namespace QuaternionicSymmetry.SelectedTorusLieSpanDerivativeRange

open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open SelectedTorusEmbeddedLieAtlas SelectedTorusSmoothCurveLift
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

theorem curve_velocity_mem_derivative_range
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    {v : GroupLieAlgebra 𝓘(ℝ,V) G}
    (hv : v ∈ torusCurveVelocities (V := V) T) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    v ∈ LinearMap.range
      ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1).toLinearMap) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  obtain ⟨c,hc0,hRange,hc,hv'⟩ := hv
  let l := liftCurve T c hRange
  have hl : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ) ∞ l :=
    liftCurve_smooth T g c hRange hImm hLee hc
  have h0 : l 0 = 1 := T.injective_hom (by
    rw [liftCurve_map T c hRange 0, hc0, map_one])
  have hcomp : T.hom ∘ l = c := by
    funext s
    exact liftCurve_map T c hRange s
  have hchain := mfderiv_comp (I := 𝓘(ℝ,ℝ))
    (I' := 𝓘(ℝ,Fin d → ℝ)) (I'' := 𝓘(ℝ,V)) (x := (0 : ℝ))
    ((selected_hom_smooth T g).mdifferentiable (by simp) (l 0))
    (hl.mdifferentiable (by simp) 0)
  rw [h0, hcomp] at hchain
  refine ⟨mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ) l 0 (1 : ℝ), ?_⟩
  simpa only [ContinuousLinearMap.comp_apply, hv'] using
    (congrArg (fun F => F (1 : ℝ)) hchain).symm

theorem torusLieSpan_le_derivative_range
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    torusLieSpan (V := V) T ≤
      LinearMap.range
        ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) T.hom 1).toLinearMap) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  exact Submodule.span_le.mpr
    (fun v hv => curve_velocity_mem_derivative_range T g hImm hLee hv)

end
end QuaternionicSymmetry.SelectedTorusLieSpanDerivativeRange
