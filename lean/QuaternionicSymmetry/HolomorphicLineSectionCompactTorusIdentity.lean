import QuaternionicSymmetry.HolomorphicLineSectionIdentity
import QuaternionicSymmetry.ComplexTorusExponential

/-! Uniqueness for actual holomorphic line sections on a complex torus:
restriction to the compact torus determines the section.  The proof pulls
back through surjective holomorphic exponential parameters, retaining the
actual bundle transition functions throughout. -/

namespace QuaternionicSymmetry.HolomorphicLineSectionCompactTorusIdentity

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ComplexTorusExponential ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section
universe u

theorem zero_of_compact {r : ℕ}
    (L : LineCore.{u} (B := ComplexTorus r) 𝓘(ℂ, Fin r → ℂ))
    (s : GlobalSections 𝓘(ℂ, Fin r → ℂ) L)
    (hcompact : ∀ t : Torus r, s (compactInclusion r t) = 0) :
    ∀ z, s z = 0 := by
  let K := pullbackLineCore 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, Fin r → ℂ)
    L (exponential r) (exponential_contMDiff r)
  let s' := restrictSection 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, Fin r → ℂ)
    L (exponential r) (exponential_contMDiff r) s
  have hreal : ∀ t : Fin r → ℝ, s' (fun i => (t i : ℂ)) = 0 := by
    intro t
    change s (exponential r (fun i => (t i : ℂ))) = 0
    rw [exponential_real]
    exact hcompact _
  have hall := HolomorphicLineSectionIdentity.zero_of_real_pi K s' hreal
  intro z
  obtain ⟨w, rfl⟩ := exponential_surjective r z
  exact hall w

end
end QuaternionicSymmetry.HolomorphicLineSectionCompactTorusIdentity
