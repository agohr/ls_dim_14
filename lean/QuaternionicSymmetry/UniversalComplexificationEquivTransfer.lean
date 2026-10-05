import QuaternionicSymmetry.CompactRealFormUniversalComplexification

/-! The universal complexification property is invariant under a
homeomorphic equivalence of its real source group. -/

namespace QuaternionicSymmetry.UniversalComplexificationEquivTransfer

open CompactRealFormUniversalComplexification
open scoped Manifold ContDiff

variable {K K' G VC : Type} [Group K] [TopologicalSpace K]
  [Group K'] [TopologicalSpace K']
  [Group G] [TopologicalSpace G]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC]
  [ChartedSpace VC G] [LieGroup 𝓘(ℂ,VC) ∞ G]

theorem precomp (ι : K →* G) (e : K' ≃* K)
    (he : Continuous e) (he' : Continuous e.symm)
    (hι : IsUniversalComplexification (VC := VC) ι) :
    IsUniversalComplexification (VC := VC) (ι.comp e.toMonoidHom) := by
  rcases hι with ⟨hcont, hinj, huniv⟩
  refine ⟨hcont.comp he, hinj.comp e.injective, ?_⟩
  intro W H _ _ _ _ _ _ _ _ _ f hf
  let fK : K →* H := f.comp e.symm.toMonoidHom
  obtain ⟨Φ, hΦ, huniq⟩ := huniv (W := W) (H := H) fK (hf.comp he')
  refine ⟨Φ, ?_, ?_⟩
  · refine ⟨hΦ.1, ?_⟩
    apply MonoidHom.ext
    intro x
    have hx := congrArg (fun g : K →* H => g (e x)) hΦ.2
    simpa [fK, MonoidHom.comp_apply] using hx
  · intro Ψ hΨ
    apply huniq
    refine ⟨hΨ.1, ?_⟩
    apply MonoidHom.ext
    intro x
    have hx := congrArg (fun g : K' →* H => g (e.symm x)) hΨ.2
    simpa [fK, MonoidHom.comp_apply] using hx

end QuaternionicSymmetry.UniversalComplexificationEquivTransfer
