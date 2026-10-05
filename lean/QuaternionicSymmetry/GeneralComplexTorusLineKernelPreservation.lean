import QuaternionicSymmetry.HolomorphicLineAlongMapCompactTorusIdentity
import QuaternionicSymmetry.HolomorphicParameterTangent

/-! A jointly holomorphic complex-torus family preserves the kernel of a
holomorphic line-valued one-form whenever its compact-torus restriction
does. This applies to contact forms but does not require nondegeneracy. -/

namespace QuaternionicSymmetry.GeneralComplexTorusLineKernelPreservation

open HolomorphicLineCoreClasses HolomorphicParameterTangent
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section
universe u

variable {Z V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ, V) ∞ Z]

theorem preserves_kernel {r : ℕ}
    (L : LineCore.{u} (B := Z) 𝓘(ℂ, V))
    (θ : ∀ z, TangentSpace 𝓘(ℂ, V) z →ₗ[ℂ] L.core.Fiber z)
    (hθ : letI := L.holomorphic
      ContMDiff (𝓘(ℂ, V)).tangent (𝓘(ℂ, V).prod 𝓘(ℂ, ℂ)) ∞
        (fun t : TangentBundle 𝓘(ℂ, V) Z =>
          (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.core.Fiber)))
    (F : ComplexTorus r × Z → Z)
    (hF : ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) ∞ F)
    (hcompact : ∀ (t : Torus r) (z : Z) (v : TangentSpace 𝓘(ℂ, V) z),
      θ z v = 0 → θ (F (compactInclusion r t, z))
        (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V)
          (fun y => F (compactInclusion r t, y)) z v) = 0) :
    ∀ (g : ComplexTorus r) (z : Z) (v : TangentSpace 𝓘(ℂ, V) z),
      θ z v = 0 → θ (F (g, z))
        (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) (fun y => F (g, y)) z v) = 0 := by
  letI := L.holomorphic
  intro g z v hv
  let f : ComplexTorus r → Z := fun p => F (p, z)
  have hf : ContMDiff 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, V) ∞ f :=
    hF.comp (contMDiff_id.prodMk contMDiff_const)
  let s : ∀ p, L.core.Fiber (f p) := fun p =>
    θ (F (p, z)) (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) (fun y => F (p, y)) z v)
  have hs : ContMDiff 𝓘(ℂ, Fin r → ℂ) (𝓘(ℂ, V).prod 𝓘(ℂ, ℂ)) ∞
      (fun p => (⟨f p, s p⟩ : Bundle.TotalSpace ℂ L.core.Fiber)) :=
    hθ.comp (parameterTangent_contMDiff F hF z v)
  exact HolomorphicLineAlongMapCompactTorusIdentity.zero_of_compact
    𝓘(ℂ, V) L f hf s hs (fun t => hcompact t z v hv) g

end
end QuaternionicSymmetry.GeneralComplexTorusLineKernelPreservation
