import QuaternionicSymmetry.HolomorphicLineCoreAmpleness

/-! Scalar action on sections of an actual very ample line forces the
underlying base map to be the identity. This is a point-separation argument
for the constructed complete linear system, not an assumed faithful
linearization. Application to an ample line requires an actual section
action on a very ample tensor power. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveFaithfulness

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{u} (B := B) IB)

/-- A scalar section transformation compatible with genuine fiber maps
fixes every point of the complete projective evaluation image. -/
theorem projectiveEvaluation_fixed_of_scalar_sectionMap
    (f : B → B)
    (Φ : ∀ x : B, L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (f x))
    (T : GlobalSections IB L →ₗ[ℂ] GlobalSections IB L)
    (hT : ∀ (s : GlobalSections IB L) (x : B), (T s) (f x) = Φ x (s x))
    (c : ℂˣ) (hc : ∀ s : GlobalSections IB L, T s = (c : ℂ) • s)
    (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L) (x : B) :
    projectiveEvaluationOfGenerated IB L d b hGen (f x) =
      projectiveEvaluationOfGenerated IB L d b hGen x := by
  have hx : x ∉ baseLocus IB L := by
    simp [(globallyGenerated_iff_baseLocus_empty IB L).1 hGen]
  have hfx : f x ∉ baseLocus IB L := by
    simp [(globallyGenerated_iff_baseLocus_empty IB L).1 hGen]
  let φ : ℂ ≃ₗ[ℂ] ℂ := Φ x
  let ev : GlobalSections IB L → B → ℂ := fun s y => s y
  have hvalue (s : GlobalSections IB L) :
      ev s (f x) = (c : ℂ)⁻¹ * φ 1 * ev s x := by
    have hn := hT s x
    rw [hc] at hn
    change (c : ℂ) * ev s (f x) = φ (ev s x) at hn
    have hΦ : φ (ev s x) = φ 1 * ev s x := by
      have h := φ.map_smul (ev s x) (1 : ℂ)
      simpa [smul_eq_mul, mul_comm] using h
    rw [hΦ] at hn
    calc
      ev s (f x) = (c : ℂ)⁻¹ * ((c : ℂ) * ev s (f x)) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * (φ 1 * ev s x) := by rw [hn]
      _ = _ := (mul_assoc _ _ _).symm
  change Projectivization.mk ℂ (basisEvaluation IB L d b (f x))
      (basisEvaluation_ne_zero IB L d b hfx) =
    Projectivization.mk ℂ (basisEvaluation IB L d b x)
      (basisEvaluation_ne_zero IB L d b hx)
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(c : ℂ)⁻¹ * φ 1, ?_⟩
  funext k
  exact (hvalue (b k)).symm

/-- Actual very ampleness detects the base map even when its action on
all sections is an arbitrary nonzero scalar rather than the identity. -/
theorem baseMap_eq_id_of_scalar_sectionMap [IsManifold IB ∞ B]
    (hVery : VeryAmpleCore IB L)
    (f : B → B)
    (Φ : ∀ x : B, L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (f x))
    (T : GlobalSections IB L →ₗ[ℂ] GlobalSections IB L)
    (hT : ∀ (s : GlobalSections IB L) (x : B), (T s) (f x) = Φ x (s x))
    (c : ℂˣ) (hc : ∀ s : GlobalSections IB L, T s = (c : ℂ) • s) :
    f = id := by
  obtain ⟨d, b, hGen, hemb, _⟩ := hVery
  funext x
  exact hemb.injective
    (projectiveEvaluation_fixed_of_scalar_sectionMap IB L f Φ T hT c hc d b hGen x)

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveFaithfulness
