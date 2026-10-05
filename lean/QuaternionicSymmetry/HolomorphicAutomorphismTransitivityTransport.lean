import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphisms

/-! Holomorphic point transitivity is invariant under a genuine
biholomorphism. The conjugated maps are actual manifold diffeomorphisms,
not an assumed action on the target. -/

namespace QuaternionicSymmetry.HolomorphicAutomorphismTransitivityTransport
open GeneralHolomorphicFullAutomorphisms
open GeneralHolomorphicDistributionAutomorphisms
open scoped Manifold ContDiff
noncomputable section

variable {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace V X] [ChartedSpace V Y]
  [IsManifold 𝓘(ℂ,V) ∞ X] [IsManifold 𝓘(ℂ,V) ∞ Y]

def conjugate (e : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) X Y ∞)
    (f : HolomorphicAutomorphisms V X) : HolomorphicAutomorphisms V Y := by
  refine ⟨(e.symm.trans f.1).trans e, ?_⟩
  constructor <;> intro z v hv <;> trivial

theorem conjugate_apply (e : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) X Y ∞)
    (f : HolomorphicAutomorphisms V X) (y : Y) :
    (conjugate e f).1 y = e (f.1 (e.symm y)) := rfl

theorem transitive_of_biholomorph
    (e : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) X Y ∞)
    (hTrans : ∀ x w : X, ∃ f : HolomorphicAutomorphisms V X,
      f.1 x = w) :
    ∀ y w : Y, ∃ f : HolomorphicAutomorphisms V Y,
      f.1 y = w := by
  intro y w
  obtain ⟨f,hf⟩ := hTrans (e.symm y) (e.symm w)
  refine ⟨conjugate e f, ?_⟩
  rw [conjugate_apply, hf, e.apply_symm_apply]

end
end QuaternionicSymmetry.HolomorphicAutomorphismTransitivityTransport
