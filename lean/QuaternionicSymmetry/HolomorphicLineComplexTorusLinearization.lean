import QuaternionicSymmetry.HolomorphicLineCoreComplexTorusExtension
import QuaternionicSymmetry.ComplexTorusHolomorphicStructure

/-! A genuine holomorphic linearization of a represented complex line under
a complex torus. This is independent of projective generation, ampleness,
Fano/Picard claims, and algebraic source/sink conclusions. -/
namespace QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

universe u
variable {X F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F X]
  (L : LineCore.{u} (B := X) 𝓘(ℂ,F)) {r : ℕ}

/-- The actual bundle-total action induced by a point action and
complex-linear maps between its genuine fibers. -/
def lineTotalMap
    (ρ : ComplexTorus r →* Equiv.Perm X)
    (Φ : ∀ (t : ComplexTorus r) (x : X),
      L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (ρ t x))
    (t : ComplexTorus r)
    (v : Bundle.TotalSpace ℂ L.core.Fiber) :
    Bundle.TotalSpace ℂ L.core.Fiber :=
  ⟨ρ t v.1, Φ t v.1 v.2⟩

/-- An analytic line linearization, with laws on the actual dependent
bundle total space. Identity and multiplication are checked on all fibers;
joint holomorphicity is on the independently charted vector-bundle total
space, not merely on preferred scalar coefficients. -/
structure ComplexTorusLineLinearization where
  baseAction : ComplexTorus r →* Equiv.Perm X
  fiberEquiv : ∀ (t : ComplexTorus r) (x : X),
    L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (baseAction t x)
  one_total : ∀ v : Bundle.TotalSpace ℂ L.core.Fiber,
    lineTotalMap L baseAction fiberEquiv 1 v = v
  mul_total : ∀ (s t : ComplexTorus r)
      (v : Bundle.TotalSpace ℂ L.core.Fiber),
    lineTotalMap L baseAction fiberEquiv (s * t) v =
      lineTotalMap L baseAction fiberEquiv s
        (lineTotalMap L baseAction fiberEquiv t v)
  joint_holomorphic :
    letI := L.holomorphic
    letI : ContMDiffVectorBundle ∞ ℂ L.core.Fiber 𝓘(ℂ,F) :=
      VectorBundleCore.instContMDiffVectorBundle L.core
    ContMDiff
      (𝓘(ℂ,Fin r → ℂ).prod (𝓘(ℂ,F).prod 𝓘(ℂ,ℂ)))
      (𝓘(ℂ,F).prod 𝓘(ℂ,ℂ)) ∞
      (fun p : ComplexTorus r × Bundle.TotalSpace ℂ L.core.Fiber =>
        lineTotalMap L baseAction fiberEquiv p.1 p.2)

end
end QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization
