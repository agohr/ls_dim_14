import QuaternionicSymmetry.ComplexProjectiveAffineTransitions
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! The standard affine charted-space structure on finite-dimensional complex
projective space, built from the quotient-topology homeomorphisms. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open scoped Manifold

noncomputable def projectiveChart (d : ℕ) (i : Fin (d + 1)) :
    OpenPartialHomeomorph (Space d) (Fin d → ℂ) :=
  ((TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
    ⟨affineDomain d i, isOpen_affineDomain d i⟩
    ⟨(affineEuclideanHomeomorph d i).symm 0⟩).symm).transHomeomorph
      (affineEuclideanHomeomorph d i)

theorem projectiveChart_source (d : ℕ) (i : Fin (d + 1)) :
    (projectiveChart d i).source = affineDomain d i := by
  simp [projectiveChart]

theorem projectiveChart_target (d : ℕ) (i : Fin (d + 1)) :
    (projectiveChart d i).target = Set.univ := by
  simp [projectiveChart]

theorem projectiveChart_apply (d : ℕ) (i : Fin (d + 1))
    (p : Space d) (hp : p ∈ affineDomain d i) :
    projectiveChart d i p = affineEuclideanHomeomorph d i ⟨p, hp⟩ := by
  let s : TopologicalSpace.Opens (Space d) :=
    ⟨affineDomain d i, isOpen_affineDomain d i⟩
  let e := s.openPartialHomeomorphSubtypeCoe
    ⟨(affineEuclideanHomeomorph d i).symm 0⟩
  have he : e (e.symm p) = p := e.right_inv (by simpa [e, s] using hp)
  have hval : (e.symm p).1 = p := by simpa [e] using he
  have hsub : e.symm p = (⟨p, hp⟩ : affineDomain d i) :=
    Subtype.ext hval
  change (affineEuclideanHomeomorph d i) (e.symm p) = _
  rw [hsub]

theorem projectiveChart_symm_apply (d : ℕ) (i : Fin (d + 1))
    (w : Fin d → ℂ) :
    (projectiveChart d i).symm w = euclideanPoint d i w := by
  rfl

theorem projectiveChart_transition_source (d : ℕ)
    (i j : Fin (d + 1)) :
    ((projectiveChart d i).symm.trans (projectiveChart d j)).source =
      euclideanOverlap d i j := by
  rw [OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, projectiveChart_target]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage]
  rw [projectiveChart_symm_apply, projectiveChart_source]
  exact euclideanPoint_mem_j_iff d i j w

theorem projectiveChart_transition_apply (d : ℕ)
    (i j : Fin (d + 1)) (w : Fin d → ℂ)
    (hw : w ∈ euclideanOverlap d i j) :
    ((projectiveChart d i).symm.trans (projectiveChart d j)) w =
      euclideanTransition d i j w := by
  rw [OpenPartialHomeomorph.trans_apply, projectiveChart_symm_apply]
  rw [projectiveChart_apply d j _ ((euclideanPoint_mem_j_iff d i j w).2 hw)]
  exact (euclideanTransition_eq_chart d i j w hw).symm

/-- The chosen atlas consists exactly of the finitely many standard affine
charts; their sources cover projective space. -/
noncomputable instance (d : ℕ) : ChartedSpace (Fin d → ℂ) (Space d) where
  atlas := Set.range (projectiveChart d)
  chartAt p := projectiveChart d (Classical.choose (exists_mem_affineDomain d p))
  mem_chart_source p := by
    rw [projectiveChart_source]
    exact Classical.choose_spec (exists_mem_affineDomain d p)
  chart_mem_atlas p := ⟨_, rfl⟩

end QuaternionicSymmetry.ComplexProjectiveTopology
