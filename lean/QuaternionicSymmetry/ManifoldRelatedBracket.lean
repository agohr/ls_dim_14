import QuaternionicSymmetry.ManifoldChartRelatedFields
import QuaternionicSymmetry.VectorFieldRelatedBracket

/-! Naturalness of the actual manifold Lie bracket under a smooth map
relating two pairs of vector fields. No inverse derivative, immersion,
or literature premise is required for the map itself. -/

namespace QuaternionicSymmetry.ManifoldRelatedBracket

open ManifoldChartVectorField ManifoldChartRelatedFields VectorField
open scoped Manifold ContDiff Topology
noncomputable section

variable {𝕜 E F M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(𝕜,F) ∞ N]

theorem chartField_related_of_mem_target (f : M → N)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f)
    (V : (x : M) → TangentSpace 𝓘(𝕜,E) x)
    (V' : (x : N) → TangentSpace 𝓘(𝕜,F) x)
    (hRel : ∀ p, mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f p (V p) = V' (f p))
    (x : M) {y : E} (hy : y ∈ (extChartAt 𝓘(𝕜,E) x).target)
    (hfy : f ((extChartAt 𝓘(𝕜,E) x).symm y) ∈
      (extChartAt 𝓘(𝕜,F) (f x)).source) :
    fderiv 𝕜 (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x) y
      (chartField V x y) =
      chartField V' (f x) (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x y) := by
  have htarget := chartField_apply_of_mem_target V' (f x)
    ((extChartAt 𝓘(𝕜,F) (f x)).map_source hfy)
  rw [(extChartAt 𝓘(𝕜,F) (f x)).left_inv hfy] at htarget
  change chartField V' (f x) (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x y) = _
    at htarget
  rw [htarget, chartMap_fderiv f hf x hy hfy, chartField_apply_of_mem_target V x hy]
  have hcancel := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy
  rw [show Set.range 𝓘(𝕜,E) = Set.univ by simp, mfderivWithin_univ] at hcancel
  have hc : mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x).symm y
      (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x)
        ((extChartAt 𝓘(𝕜,E) x).symm y) (V ((extChartAt 𝓘(𝕜,E) x).symm y))) =
      V ((extChartAt 𝓘(𝕜,E) x).symm y) :=
    congrArg (fun A : E →L[𝕜] E => A (V ((extChartAt 𝓘(𝕜,E) x).symm y))) hcancel
  change mfderiv 𝓘(𝕜,F) 𝓘(𝕜,F) (extChartAt 𝓘(𝕜,F) (f x))
      (f ((extChartAt 𝓘(𝕜,E) x).symm y))
      (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f ((extChartAt 𝓘(𝕜,E) x).symm y)
        (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x).symm y
          (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x)
            ((extChartAt 𝓘(𝕜,E) x).symm y) (V ((extChartAt 𝓘(𝕜,E) x).symm y))))) = _
  rw [hc, hRel]

theorem chartField_eventually_related (f : M → N)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f)
    (V : (x : M) → TangentSpace 𝓘(𝕜,E) x)
    (V' : (x : N) → TangentSpace 𝓘(𝕜,F) x)
    (hRel : ∀ p, mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f p (V p) = V' (f p)) (x : M) :
    (fun y => fderiv 𝕜 (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x) y
      (chartField V x y)) =ᶠ[𝓝 (extChartAt 𝓘(𝕜,E) x x)]
      (fun y => chartField V' (f x) (chartMap (𝕜 := 𝕜) (E := E) (F := F) f x y)) := by
  have hσ : ContinuousAt (extChartAt 𝓘(𝕜,E) x).symm
      (extChartAt 𝓘(𝕜,E) x x) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x _ (mem_extChartAt_target x)).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).continuousAt
  have hcont : Filter.Tendsto (f ∘ (extChartAt 𝓘(𝕜,E) x).symm)
      (𝓝 (extChartAt 𝓘(𝕜,E) x x)) (𝓝 (f x)) := by
    simpa only [Function.comp_apply, extChartAt_to_inv] using
      (hf.continuous.continuousAt.comp hσ).tendsto
  have htarget := hcont.eventually (extChartAt_source_mem_nhds (I := 𝓘(𝕜,F)) (f x))
  filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x),
    htarget] with y hy hfy
  exact chartField_related_of_mem_target f hf V V' hRel x hy hfy

theorem mfderiv_mlieBracket_of_related (f : M → N)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f)
    (V W : (x : M) → TangentSpace 𝓘(𝕜,E) x)
    (V' W' : (x : N) → TangentSpace 𝓘(𝕜,F) x)
    (hV : MDifferentiable 𝓘(𝕜,E) 𝓘(𝕜,E).tangent
      (fun x => (V x : TangentBundle 𝓘(𝕜,E) M)))
    (hW : MDifferentiable 𝓘(𝕜,E) 𝓘(𝕜,E).tangent
      (fun x => (W x : TangentBundle 𝓘(𝕜,E) M)))
    (hV' : MDifferentiable 𝓘(𝕜,F) 𝓘(𝕜,F).tangent
      (fun x => (V' x : TangentBundle 𝓘(𝕜,F) N)))
    (hW' : MDifferentiable 𝓘(𝕜,F) 𝓘(𝕜,F).tangent
      (fun x => (W' x : TangentBundle 𝓘(𝕜,F) N)))
    (hRelV : ∀ p, mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f p (V p) = V' (f p))
    (hRelW : ∀ p, mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f p (W p) = W' (f p)) (x : M)
    (hSmooth : minSmoothness 𝕜 2 ≤ (∞ : WithTop ℕ∞)) :
    mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f x (mlieBracket 𝓘(𝕜,E) V W x) =
      mlieBracket 𝓘(𝕜,F) V' W' (f x) := by
  have hVchart := chartField_differentiableAt (hV x)
  have hWchart := chartField_differentiableAt (hW x)
  have hV'chart := chartField_differentiableAt (hV' (f x))
  have hW'chart := chartField_differentiableAt (hW' (f x))
  have h := VectorFieldRelatedBracket.fderiv_lieBracket_of_eventually_related
    (chartMap_contDiffAt f hf x) hSmooth hVchart hWchart
    (by simpa only [chartMap_center] using hV'chart)
    (by simpa only [chartMap_center] using hW'chart)
    (chartField_eventually_related f hf V V' hRelV x)
    (chartField_eventually_related f hf W W' hRelW x)
  rw [chartMap_fderiv_center f hf x, chartMap_center,
    ← mlieBracket_eq_chart_lieBracket, ← mlieBracket_eq_chart_lieBracket] at h
  exact h

end
end QuaternionicSymmetry.ManifoldRelatedBracket
