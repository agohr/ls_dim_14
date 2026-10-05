import QuaternionicSymmetry.ComplexProjectiveChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! The standard projective affine atlas is a complex-smooth manifold atlas. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open scoped Manifold ContDiff

private theorem transition_contDiffOn (d : ℕ) (i j : Fin (d + 1)) :
    ContDiffOn ℂ ∞
      ((projectiveChart d i).symm.trans (projectiveChart d j))
      ((projectiveChart d i).symm.trans (projectiveChart d j)).source := by
  rw [projectiveChart_transition_source]
  exact (contDiffOn_euclideanTransition d i j).congr
    (fun w hw => projectiveChart_transition_apply d i j w hw)

noncomputable instance (d : ℕ) :
    IsManifold 𝓘(ℂ, Fin d → ℂ) ∞ (Space d) := by
  letI : HasGroupoid (Space d) (contDiffGroupoid ∞ 𝓘(ℂ, Fin d → ℂ)) := by
    apply hasGroupoid_of_pregroupoid
    intro e e' he he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    simpa [contDiffPregroupoid] using transition_contDiffOn d i j
  exact IsManifold.mk' 𝓘(ℂ, Fin d → ℂ) ∞ (Space d)

end QuaternionicSymmetry.ComplexProjectiveTopology
