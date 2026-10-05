import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFormula
import QuaternionicSymmetry.ComplexProjectiveManifold

/-! Fixed complex-torus elements act holomorphically on the literal
projective manifold, by diagonal affine-chart formulas. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalHolomorphic

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalChartFormula TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

def chartDiagonal {r d : ℕ} (μ : Fin (d + 1) → Fin r → ℤ)
    (z : ComplexTorus r) (i : Fin (d + 1))
    (w : Fin d → ℂ) : Fin d → ℂ :=
  fun k => ((complexWeightCharacter (μ (i.succAbove k)) z : ℂ) /
    (complexWeightCharacter (μ i) z : ℂ)) * w k

theorem contDiff_chartDiagonal {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (i : Fin (d + 1)) : ContDiff ℂ ∞ (chartDiagonal μ z i) := by
  apply contDiff_pi.mpr
  intro k
  exact (contDiff_const.mul (contDiff_apply ℂ ℂ k))

theorem chart_projectiveAction {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (i : Fin (d + 1)) (p : Space d) (hp : p ∈ affineDomain d i) :
    projectiveChart d i (projectiveAction μ z p) =
      chartDiagonal μ z i (projectiveChart d i p) := by
  rw [projectiveChart_apply d i _
    ((projectiveAction_mem_affineDomain_iff μ z i p).2 hp),
    projectiveChart_apply d i p hp]
  funext k
  change affineRatio d i
      ⟨projectiveAction μ z p,
        (projectiveAction_mem_affineDomain_iff μ z i p).2 hp⟩
      (i.succAbove k) =
    ((complexWeightCharacter (μ (i.succAbove k)) z : ℂ) /
      (complexWeightCharacter (μ i) z : ℂ)) *
      affineRatio d i ⟨p, hp⟩ (i.succAbove k)
  exact affineRatio_projectiveAction μ z i (i.succAbove k) p hp

theorem contMDiffOn_projectiveAction_chart {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r)
    (i : Fin (d + 1)) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ∞
      (projectiveAction μ z) (affineDomain d i) := by
  have he : projectiveChart d i ∈
      (contDiffGroupoid ∞ 𝓘(ℂ, Fin d → ℂ)).maximalAtlas (Space d) :=
    (StructureGroupoid.subset_maximalAtlas
      (G := contDiffGroupoid ∞ 𝓘(ℂ, Fin d → ℂ))) ⟨i, rfl⟩
  have hmap : Set.MapsTo (projectiveAction μ z)
      (affineDomain d i) (projectiveChart d i).source := by
    intro p hp
    rw [projectiveChart_source]
    exact (projectiveAction_mem_affineDomain_iff μ z i p).2 hp
  apply (contMDiffOn_iff_of_mem_maximalAtlas' he he
    (by simp [projectiveChart_source]) hmap).mpr
  have hcomp : ContDiffOn ℂ ∞
      (fun w : Fin d → ℂ =>
        projectiveChart d i
          (projectiveAction μ z ((projectiveChart d i).symm w)))
      ((projectiveChart d i) '' (affineDomain d i)) := by
    apply (contDiff_chartDiagonal μ z i).contDiffOn.congr
    intro w hw
    have htarget : w ∈ (projectiveChart d i).target := by
      rw [projectiveChart_target]
      trivial
    have hs : (projectiveChart d i).symm w ∈ affineDomain d i := by
      rw [← projectiveChart_source]
      exact (projectiveChart d i).map_target htarget
    rw [chart_projectiveAction μ z i _ hs]
    rw [(projectiveChart d i).right_inv htarget]
  simpa [projectiveChart_source, projectiveChart_target] using hcomp

theorem contMDiff_projectiveAction {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ∞
      (projectiveAction μ z) := by
  apply contMDiffOn_univ.mp
  apply contMDiffOn_of_locally_contMDiffOn
  intro p hp
  obtain ⟨i, hi⟩ := exists_mem_affineDomain d p
  refine ⟨affineDomain d i, isOpen_affineDomain d i, hi, ?_⟩
  exact (contMDiffOn_projectiveAction_chart μ z i).mono Set.inter_subset_right

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalHolomorphic
