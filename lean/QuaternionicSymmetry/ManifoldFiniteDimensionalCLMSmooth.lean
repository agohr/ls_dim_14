import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! A finite-dimensional test for smooth continuous-linear-map-valued fields
on an arbitrary smooth manifold. This is the local-chart version of Mathlib's
`contDiffOn_clm_apply`. -/

namespace QuaternionicSymmetry.ManifoldFiniteDimensionalCLMSmooth

open scoped Manifold ContDiff
noncomputable section

variable {F H N A B : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem contMDiffOn_clm_apply_iff {s : Set N} (hs : IsOpen s)
    {f : N → A →L[ℝ] B} :
    ContMDiffOn I 𝓘(ℝ,A →L[ℝ] B) ∞ f s ↔
      ∀ a : A, ContMDiffOn I 𝓘(ℝ,B) ∞ (fun x => f x a) s := by
  constructor
  · intro hf a
    exact hf.clm_apply contMDiffOn_const
  · intro hf x hx
    let e := extChartAt I x
    let U : Set N := s ∩ e.source
    let t : Set F := e.target ∩ e.symm ⁻¹' s
    have hU : IsOpen U := hs.inter (isOpen_extChartAt_source x)
    have hux : x ∈ U := ⟨hx, mem_extChartAt_source x⟩
    have hsymm : ContMDiffOn 𝓘(ℝ,F) I ∞ e.symm t :=
      (contMDiffOn_extChartAt_symm x).mono (Set.inter_subset_left)
    have hmapSymm : Set.MapsTo e.symm t s := by
      intro y hy
      exact hy.2
    have hscalar (a : A) : ContDiffOn ℝ ∞
        (fun y : F => f (e.symm y) a) t :=
      ((hf a).comp hsymm hmapSymm).contDiffOn
    have hfield : ContDiffOn ℝ ∞ (f ∘ e.symm) t :=
      contDiffOn_clm_apply.mpr hscalar
    have he : ContMDiffOn I 𝓘(ℝ,F) ∞ e U :=
      (contMDiffOn_extChartAt (I := I) (x := x)).mono (by
        intro y hy
        simpa only [← extChartAt_source I] using hy.2)
    have hmapE : Set.MapsTo e U t := by
      intro y hy
      refine ⟨e.map_source hy.2, ?_⟩
      change e.symm (e y) ∈ s
      rw [e.left_inv hy.2]
      exact hy.1
    have hcomp : ContMDiffOn I 𝓘(ℝ,A →L[ℝ] B) ∞
        (f ∘ e.symm ∘ e) U :=
      hfield.contMDiffOn.comp he hmapE
    have hlocal : ContMDiffOn I 𝓘(ℝ,A →L[ℝ] B) ∞ f U :=
      hcomp.congr (by
        intro y hy
        change f y = f (e.symm (e y))
        rw [e.left_inv hy.2])
    exact ((hlocal x hux).contMDiffAt (hU.mem_nhds hux)).contMDiffWithinAt

end
end QuaternionicSymmetry.ManifoldFiniteDimensionalCLMSmooth
