import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! A smooth map with bijective derivative is locally open, by the inverse
function theorem in actual manifold charts. No Riemannian input is used. -/
namespace QuaternionicSymmetry.ManifoldLocalDiffeomorphism
open Set Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

lemma map_nhds_eq_of_bijective_mfderiv {f : M → N} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x)
    (hb : Function.Bijective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) :
    Filter.map f (𝓝 x) = 𝓝 (f x) := by
  let φ := writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,F) x f
  let cx := extChartAt 𝓘(ℝ,E) x x
  let D : E →L[ℝ] F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x
  let L : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective D.toLinearMap hb).toContinuousLinearEquiv
  have hcd : ContDiffAt ℝ ∞ φ cx := by
    simpa [φ, cx] using (contMDiffAt_iff.mp hf).2
  have hd : HasFDerivAt φ (L : E →L[ℝ] F) cx := by
    have h := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.2
    simpa [φ, cx, L, D] using h
  have hmap := (hcd.hasStrictFDerivAt' hd (by simp)).map_nhds_eq_of_equiv
  have hs : Filter.map (extChartAt 𝓘(ℝ,E) x).symm (𝓝 cx) = 𝓝 x := by
    simpa [cx] using (map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ,E)) x)
  have ht : Filter.map (extChartAt 𝓘(ℝ,F) (f x)).symm
      (𝓝 (φ cx)) = 𝓝 (f x) := by
    simpa [φ, cx, writtenInExtChartAt] using
      (map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ,F)) (f x))
  have hc : ContinuousAt (f ∘ (extChartAt 𝓘(ℝ,E) x).symm) cx := by
    apply ContinuousAt.comp_of_eq hf.continuousAt (continuousAt_extChartAt_symm x)
    exact extChartAt_to_inv x
  have he : ((extChartAt 𝓘(ℝ,F) (f x)).symm ∘ φ) =ᶠ[𝓝 cx]
      (f ∘ (extChartAt 𝓘(ℝ,E) x).symm) := by
    have hm : ∀ᶠ y in 𝓝 cx,
        f ((extChartAt 𝓘(ℝ,E) x).symm y) ∈ (extChartAt 𝓘(ℝ,F) (f x)).source := by
      have hmem := extChartAt_source_mem_nhds (I := 𝓘(ℝ,F)) (f x)
      have hc' : Tendsto (f ∘ (extChartAt 𝓘(ℝ,E) x).symm) (𝓝 cx) (𝓝 (f x)) := by
        simpa [cx, Function.comp_def] using hc.tendsto
      exact hc' hmem
    filter_upwards [hm] with y hy
    exact (extChartAt 𝓘(ℝ,F) (f x)).left_inv hy
  calc
    Filter.map f (𝓝 x) =
        Filter.map (f ∘ (extChartAt 𝓘(ℝ,E) x).symm) (𝓝 cx) := by
      rw [← Filter.map_map, hs]
    _ = Filter.map ((extChartAt 𝓘(ℝ,F) (f x)).symm ∘ φ) (𝓝 cx) :=
      Filter.map_congr he.symm
    _ = Filter.map (extChartAt 𝓘(ℝ,F) (f x)).symm (𝓝 (φ cx)) := by
      rw [← Filter.map_map, hmap]
    _ = 𝓝 (f x) := ht

lemma isOpenMap_of_bijective_mfderiv {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hb : ∀ x, Function.Bijective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) : IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  exact le_of_eq (map_nhds_eq_of_bijective_mfderiv x (hf x) (hb x)).symm


end
end QuaternionicSymmetry.ManifoldLocalDiffeomorphism
