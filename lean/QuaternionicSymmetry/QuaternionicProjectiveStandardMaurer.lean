import QuaternionicSymmetry.QuaternionicProjectiveProductMaurer

/-! The standard infinitesimal representation carries the tangent
factorization's Maurer--Cartan form to the block standard one. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardMaurer

open scoped Quaternion Topology
open QuaternionicProjectiveProductMaurer
open QuaternionicProjectiveLineMaurer
open QuaternionicProjectiveKernelMaurer
open QuaternionicProjectiveStandardLie
open QuaternionicProjectiveStandardLieBracket
open QuaternionicLieAlgebraProjection
open VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem scalarLineLie_eq_zero_of_commutes (S : QuaternionicStructure E)
    (A : E →L[ℝ] E)
    (hA : ∀ a : Fin 3 → ℝ, A * synth S a = synth S a * A) :
    scalarLineLie S A = 0 := by
  rw [← scalarLineLie_scalarProjection S A,
    scalarProjection_eq_zero_of_commutes S A hA, map_zero]

theorem standardMaurer_kernel_block (S : QuaternionicStructure E)
    (q : X → ℍ) (h : X → E →L[ℝ] E) (x u : X)
    (hq : DifferentiableAt ℝ q x) (hh : DifferentiableAt ℝ h x)
    (hunit : ∀ᶠ y in 𝓝 x, star (q y) * q y = 1)
    (hright : q x * star (q x) = 1)
    (hInv : E →L[ℝ] E) (hleft : hInv * h x = 1)
    (hc : ∀ a : Fin 3 → ℝ,
      ∀ᶠ y in 𝓝 x, h y * synth S a = synth S a * h y)
    (hInvC : ∀ a : Fin 3 → ℝ,
      hInv * synth S a = synth S a * hInv) :
    symplecticProjection S
        ((hInv * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
          (star (q x))) * fderiv ℝ (productGauge S q h) x u) =
      hInv * fderiv ℝ h x u := by
  rw [productGauge_maurer_of_kernel S q h x u hq hh hunit hright hInv hleft hInvC,
    map_add]
  have hpure := star_mul_fderiv_pure q x hq hunit hright u
  rw [scalarAction_pure_eq_synth S _ hpure,
    ← scalarProjection_synth S _, symplecticProjection_scalarProjection]
  simp only [zero_add]
  exact symplecticProjection_left_mul_fderiv S h hInv x u hh hc hInvC

theorem standardMaurer_line_block (S : QuaternionicStructure E)
    (q : X → ℍ) (h : X → E →L[ℝ] E) (x u : X)
    (hq : DifferentiableAt ℝ q x) (hh : DifferentiableAt ℝ h x)
    (hunit : ∀ᶠ y in 𝓝 x, star (q y) * q y = 1)
    (hright : q x * star (q x) = 1)
    (hInv : E →L[ℝ] E) (hleft : hInv * h x = 1)
    (hc : ∀ a : Fin 3 → ℝ,
      ∀ᶠ y in 𝓝 x, h y * synth S a = synth S a * h y)
    (hInvC : ∀ a : Fin 3 → ℝ,
      hInv * synth S a = synth S a * hInv) :
    scalarLineLie S
        ((hInv * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
          (star (q x))) * fderiv ℝ (productGauge S q h) x u) =
      rightStar (star (q x)) * fderiv ℝ (fun y => rightStar (q y)) x u := by
  rw [productGauge_maurer_of_kernel S q h x u hq hh hunit hright hInv hleft hInvC,
    map_add]
  have hzero : scalarLineLie S (hInv * fderiv ℝ h x u) = 0 := by
    exact scalarLineLie_eq_zero_of_commutes S _ (by
      intro a
      rw [mul_assoc, fderiv_commutes_synth S h x u hh hc a,
        ← mul_assoc, hInvC a, mul_assoc])
  rw [hzero, add_zero]
  exact (rightStar_maurer_eq_scalarLineLie S q x hq hunit hright u).symm

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardMaurer
