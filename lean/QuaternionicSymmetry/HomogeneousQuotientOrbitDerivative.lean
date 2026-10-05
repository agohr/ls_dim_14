import QuaternionicSymmetry.GeneralLieHomogeneousSpaceSource

/-! Internal geometric consequences on actual Lie-group cosets: the
canonical action is transitive, and each orbit map is a submersion. The
latter follows from the checked quotient submersion and an actual right
translation derivative, not a separately assumed tangent-generation fact. -/

namespace QuaternionicSymmetry.HomogeneousQuotientOrbitDerivative

open GeneralLieHomogeneousSpaceSource
open scoped Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

variable {G : Type} [Group G]

theorem leftCosetAction_coe (H : Subgroup G) (u a : G) :
    leftCosetAction H u (a : G ⧸ H) = ((u * a : G) : G ⧸ H) := rfl

/-- Transitivity on the actual quotient, with an explicit group element
obtained from representatives of its two genuine cosets. -/
theorem leftCosetAction_transitive (H : Subgroup G) (x y : G ⧸ H) :
    ∃ u : G, leftCosetAction H u x = y := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  refine ⟨b * a⁻¹, ?_⟩
  rw [leftCosetAction_coe, inv_mul_cancel_right]

variable [TopologicalSpace G] {d : ℕ} [ChartedSpace (RModel d) G]
  [IsManifold 𝓘(ℝ,RModel d) ∞ G] [LieGroup 𝓘(ℝ,RModel d) ∞ G]

/-- Right multiplication has a surjective actual manifold derivative,
using right multiplication by the inverse as a differentiated inverse. -/
theorem mfderiv_mul_right_surjective (a u : G) :
    Function.Surjective (mfderiv 𝓘(ℝ,RModel d) 𝓘(ℝ,RModel d)
      (fun g : G => g * a) u) := by
  intro w
  let L := mfderiv 𝓘(ℝ,RModel d) 𝓘(ℝ,RModel d)
    (fun g : G => g * a⁻¹) (u * a)
  refine ⟨L w, ?_⟩
  have h := mfderiv_comp (u * a)
    (mdifferentiableAt_mul_right (I := 𝓘(ℝ,RModel d)) (a := a))
    (mdifferentiableAt_mul_right (I := 𝓘(ℝ,RModel d)) (a := a⁻¹))
  have hfun : (fun g : G => g * a) ∘ (fun g : G => g * a⁻¹) = id := by
    funext g
    simp
  rw [hfun, mfderiv_id, mul_inv_cancel_right] at h
  exact (congrArg (fun T : RModel d →L[ℝ] RModel d => T w) h).symm

/-- Every orbit map of the canonical action on an actual homogeneous
quotient is submersive at every group point. This is an internal deduction
from Lee's quotient submersion, not an additional source conclusion. -/
theorem orbitMap_mfderiv_surjective
    (H : Subgroup G) {e q : ℕ} (A : SmoothQuotientAtlas G d H e q)
    (x : G ⧸ H) (u : G) :
    letI := A.charts
    Function.Surjective (mfderiv 𝓘(ℝ,RModel d) 𝓘(ℝ,RModel q)
      (fun g : G => leftCosetAction H g x) u) := by
  letI := A.charts
  letI := A.manifold
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  have hfun : (fun g : G => leftCosetAction H g (a : G ⧸ H)) =
      (fun g : G => (g : G ⧸ H)) ∘ (fun g : G => g * a) := rfl
  rw [hfun, mfderiv_comp u
    (A.quotientSmooth.mdifferentiableAt (by simp))
    (mdifferentiableAt_mul_right (I := 𝓘(ℝ,RModel d)))]
  exact (A.quotientSubmersive (u * a)).comp (mfderiv_mul_right_surjective a u)

end
end QuaternionicSymmetry.HomogeneousQuotientOrbitDerivative
