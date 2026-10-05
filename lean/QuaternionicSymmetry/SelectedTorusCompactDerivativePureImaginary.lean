import QuaternionicSymmetry.SelectedTorusCompactInclusionImmersion
import QuaternionicSymmetry.ComplexTorusRealChartDerivative
import QuaternionicSymmetry.UnitCircleCurveRealVelocity
import QuaternionicSymmetry.GlobalSmoothTangentCurve

/-! The real differential of the literal selected compact inclusion has
purely imaginary coordinate values. No dimension conclusion is asserted
here; this is the analytic input for `d ≤ r`. -/

namespace QuaternionicSymmetry.SelectedTorusCompactDerivativePureImaginary

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusCompactInclusionSmooth
open ComplexTorusRealChartDerivative UnitCircleCurveRealVelocity
open GlobalSmoothTangentCurve
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ComplexLieRealCompanion ComplexTorusLieGroup
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ComplexTorusCharacterHolomorphic
open ManifoldComplexHolomorphicFactorization
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ} (T : TorusEmbedding G r)
  (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)

theorem compactInclusion_derivative_re_zero
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (w : Fin d → ℝ)
    (i : Fin r) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    (((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
      (compactInclusion r) 1 w) i).re) = 0 := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  letI : T2Space (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).t2Space
  letI : SecondCountableTopology (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).secondCountableTopology
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  letI : LieGroup 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realLieGroup
  have hinc := compactInclusion_smooth T g hClosed hImm hLee
  have hval : ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,Fin r → ℂ) ∞
      (torusVal r) :=
    holomorphic_is_real_smooth (contMDiff_torusVal r)
  have hev : ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,ℂ) ∞
      (fun z : Fin r → ℂ => z i) :=
    (contDiff_apply ℝ ℂ i).contMDiff
  let F : (Fin r → Circle) → ℂ :=
    fun t => (torusVal r (compactInclusion r t)) i
  have hF : ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ) ∞ F :=
    hev.comp (hval.comp hinc)
  obtain ⟨c, hc0, hcSmooth, hcVel⟩ :=
    exists_global_smooth_curve_with_velocity (E := Fin d → ℝ)
      (M := Fin r → Circle) (1 : Fin r → Circle) w
  let f : ℝ → ℂ := F ∘ c
  have hfSmooth : ContDiff ℝ ∞ f :=
    (hF.comp hcSmooth).contDiff
  have hf0 : f 0 = 1 := by simp [f, F, hc0, torusVal, compactInclusion]
  have hunit : ∀ t, ‖f t‖ = 1 := by
    intro t
    simpa [f, F, torusVal, compactInclusion] using Circle.norm_coe (c t i)
  have hreal := real_velocity_zero f hf0 hunit
    ((hfSmooth.differentiable (by simp)) 0)
  have hcomp1 := mfderiv_comp (I := 𝓘(ℝ,ℝ))
    (I' := 𝓘(ℝ,Fin d → ℝ)) (I'' := 𝓘(ℝ,ℂ)) (x := (0 : ℝ))
    (hF.mdifferentiableAt (by simp))
    (hcSmooth.mdifferentiableAt (by simp))
  rw [hc0] at hcomp1
  have hcomp2 := mfderiv_comp (I := 𝓘(ℝ,Fin d → ℝ))
    (I' := 𝓘(ℝ,Fin r → ℂ)) (I'' := 𝓘(ℝ,ℂ))
    (x := (1 : Fin r → Circle))
    ((hev.comp hval).mdifferentiableAt (by simp))
    (hinc.mdifferentiableAt (by simp))
  have hcomp3 := mfderiv_comp (I := 𝓘(ℝ,Fin r → ℂ))
    (I' := 𝓘(ℝ,Fin r → ℂ)) (I'' := 𝓘(ℝ,ℂ))
    (x := compactInclusion r (1 : Fin r → Circle))
    (hev.mdifferentiableAt (by simp))
    (hval.mdifferentiableAt (by simp))
  -- The three chain rules reduce to the coordinate projection because
  -- torusVal is exactly the existing singleton chart.
  have hEval : mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,ℂ)
      (fun z : Fin r → ℂ => z i)
      (torusVal r (compactInclusion r (1 : Fin r → Circle))) =
      (ContinuousLinearMap.proj i : (Fin r → ℂ) →L[ℝ] ℂ) := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.proj i : (Fin r → ℂ) →L[ℝ] ℂ).hasFDerivAt.fderiv
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) f 0 = _ at hcomp1
  change mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ) F 1 = _ at hcomp2
  rw [hEval, torusVal_mfderiv_eq_id] at hcomp3
  rw [hcomp3] at hcomp2
  rw [hcomp2] at hcomp1
  have hVel := congrArg (fun L : ℝ →L[ℝ] ℂ => L (1 : ℝ)) hcomp1
  change (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) f 0 (1 : ℝ)) =
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
      (compactInclusion r) 1
        (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ) c 0 (1 : ℝ))) i at hVel
  rw [hcVel] at hVel
  rw [mfderiv_eq_fderiv] at hVel
  exact hVel ▸ hreal

end
end QuaternionicSymmetry.SelectedTorusCompactDerivativePureImaginary
