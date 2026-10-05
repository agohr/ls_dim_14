import QuaternionicSymmetry.HolomorphicLineSectionCompactTorusIdentity
import QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections

/-! Compact-torus uniqueness for holomorphic sections along a map.  This
allows the target line to vary with the actual orbit point. -/

namespace QuaternionicSymmetry.HolomorphicLineAlongMapCompactTorusIdentity

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCorePullbackLocalSections
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

theorem zero_of_compact {r : ℕ} (L : LineCore.{u} (B := B) IB)
    (f : ComplexTorus r → B)
    (hf : ContMDiff 𝓘(ℂ, Fin r → ℂ) IB ∞ f)
    (s : ∀ z, L.core.Fiber (f z))
    (hs : letI := L.holomorphic
      ContMDiff 𝓘(ℂ, Fin r → ℂ) (IB.prod 𝓘(ℂ, ℂ)) ∞
        (fun z => (⟨f z, s z⟩ : Bundle.TotalSpace ℂ L.core.Fiber)))
    (hcompact : ∀ t : Torus r, s (compactInclusion r t) = 0) :
    ∀ z, s z = 0 := by
  letI := L.holomorphic
  let K := pullbackLineCore IB 𝓘(ℂ, Fin r → ℂ) L f hf
  letI := K.holomorphic
  let s' : GlobalSections 𝓘(ℂ, Fin r → ℂ) K :=
    ⟨s, contMDiffOn_univ.mp
      (alongMap_contMDiffOn_pullback IB 𝓘(ℂ, Fin r → ℂ) L.core
        f hf Set.univ s hs.contMDiffOn)⟩
  exact HolomorphicLineSectionCompactTorusIdentity.zero_of_compact K s' hcompact

end
end QuaternionicSymmetry.HolomorphicLineAlongMapCompactTorusIdentity
