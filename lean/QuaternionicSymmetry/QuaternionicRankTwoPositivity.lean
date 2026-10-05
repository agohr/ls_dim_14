import QuaternionicSymmetry.UniversalProjectionMatrixMoments
import QuaternionicSymmetry.QuaternionicProjectionMoments
import QuaternionicSymmetry.QuaternionicAhatPositivity

/-! The explicit M32 coefficient polynomial has its pointwise quaternionic
sign, by the evaluated rank-two Haar projection moment. -/

namespace QuaternionicSymmetry.QuaternionicRankTwoPositivity

open Module QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicGaussianTraceMoments QuaternionicAhatPositivity

noncomputable section

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem M₃₂_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hr : 3 ≤ Fintype.card κ)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      ((4 / ((Fintype.card κ : ℝ) * (Fintype.card κ - 1) *
          (Fintype.card κ + 1) * (Fintype.card κ + 2))) •
        ((2 * (Fintype.card κ : ℝ) + 1) • tracePower B η 1 ^ 3 +
          (3 * ((Fintype.card κ : ℝ) - 1)) • (tracePower B η 1 * tracePower B η 2) +
          ((Fintype.card κ : ℝ) - 4) • tracePower B η 3) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 3)) := by
  have hc : 2 ≤ (Finset.univ : Finset κ).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hc
  have hp := QuaternionicProjectionMoments.moment_mixed_in_positive_ray Q c s B hB η hη 3 hk
  rw [UniversalProjectionMatrixMoments.moment_three_real s hs hr (S := CE V)] at hp
  simpa only [tracePower, pow_one] using hp

end
end QuaternionicSymmetry.QuaternionicRankTwoPositivity
