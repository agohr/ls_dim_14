import QuaternionicSymmetry.ComplexProjectiveManifold

/-! The literal complex projective atlas is also a real-smooth atlas in
the same underlying complex coordinate spaces. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open scoped Manifold ContDiff
noncomputable section

private theorem transition_real_contDiffOn (d : ℕ)
    (i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞
      ((projectiveChart d i).symm.trans (projectiveChart d j))
      ((projectiveChart d i).symm.trans (projectiveChart d j)).source := by
  rw [projectiveChart_transition_source]
  exact (contDiffOn_euclideanTransition d i j).restrict_scalars ℝ |>.congr
    (fun w hw => projectiveChart_transition_apply d i j w hw)

noncomputable instance (d : ℕ) :
    IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (Space d) := by
  letI : HasGroupoid (Space d)
      (contDiffGroupoid ∞ 𝓘(ℝ, Fin d → ℂ)) := by
    apply hasGroupoid_of_pregroupoid
    intro c c' hc hc'
    obtain ⟨i,rfl⟩ := hc
    obtain ⟨j,rfl⟩ := hc'
    simpa [contDiffPregroupoid] using transition_real_contDiffOn d i j
  exact IsManifold.mk' 𝓘(ℝ, Fin d → ℂ) ∞ (Space d)

end
end QuaternionicSymmetry.ComplexProjectiveTopology
