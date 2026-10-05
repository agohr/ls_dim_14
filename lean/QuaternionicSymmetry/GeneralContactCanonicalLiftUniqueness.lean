import QuaternionicSymmetry.GeneralContactFanoORSWRecognitionSource

/-! Source-free fidelity check for the ORSW character normalization.
The actual quotient/contact form is surjective, hence its derivative law
uniquely determines every fiber map. An independently twisted lift cannot
satisfy that same canonical law unless it is the original lift. -/
namespace QuaternionicSymmetry.GeneralContactCanonicalLiftUniqueness
open GeneralContactFanoORSWRecognitionSource GeneralComplexContactData
open ManifoldTwistorLeBrunComplexAtlas ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

variable {R H Z : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
  {n : ℕ} (G : ContactGeometry (IR := IR) (Z := Z) n) {r : ℕ}
  (a : Torus r →* Equiv.Perm Z)

theorem canonical_contactLift_unique
    (Φ Ψ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z))
    (hΦ : IsCanonicalContactLift IR G a Φ)
    (hΨ : IsCanonicalContactLift IR G a Ψ) : Φ = Ψ := by
  funext t z
  apply LinearEquiv.ext
  intro v
  obtain ⟨u,hu⟩ := G.thetaSurjective z v
  rw [← hu, hΦ, hΨ]

theorem fixedFiberCharacter_iff_of_canonical_lifts
    (Φ Ψ : ∀ t z, G.line.Fiber z ≃ₗ[ℂ] G.line.Fiber (a t z))
    (hΦ : IsCanonicalContactLift IR G a Φ)
    (hΨ : IsCanonicalContactLift IR G a Ψ)
    (z : Z) (μ : Fin r → ℤ) :
    FixedFiberCharacter IR G a Φ z μ ↔ FixedFiberCharacter IR G a Ψ z μ := by
  rw [canonical_contactLift_unique IR G a Φ Ψ hΦ hΨ]

end
end QuaternionicSymmetry.GeneralContactCanonicalLiftUniqueness
