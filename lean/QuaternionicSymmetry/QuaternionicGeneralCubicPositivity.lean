import QuaternionicSymmetry.UniversalProjectionGeneralCubic
import QuaternionicSymmetry.QuaternionicProjectionMoments
import QuaternionicSymmetry.QuaternionicAhatPositivity

/-! Every admissible cubic projection rank has its explicit pointwise
quaternionic sign. This includes the rank-three/four terms of C12. -/

namespace QuaternionicSymmetry.QuaternionicGeneralCubicPositivity

open Module QuaternionicFundamental QuaternionicTracePositivity
  QuaternionicGaussianTraceMoments QuaternionicAhatPositivity
  UniversalProjectionGeneralCubic

noncomputable section
variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem cubic_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (s : Finset κ) (hr : 3 ≤ Fintype.card κ)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (cubicValue (Fintype.card κ) s.card
        (tracePower B η 1) (tracePower B η 2) (tracePower B η 3) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 3)) := by
  have h := QuaternionicProjectionMoments.moment_mixed_in_positive_ray
    Q c s B hB η hη 3 hk
  rw [UniversalProjectionGeneralCubic.moment_three s hr] at h
  simpa only [tracePower, pow_one] using h

theorem rank_cubic_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (ell : ℕ) (hell : ell ≤ Fintype.card κ) (hr : 3 ≤ Fintype.card κ)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (cubicValue (Fintype.card κ) ell
        (tracePower B η 1) (tracePower B η 2) (tracePower B η 3) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 3)) := by
  have hc : ell ≤ (Finset.univ : Finset κ).card := by simpa using hell
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hc
  simpa only [hs] using cubic_mixed_in_positive_ray Q c s hr B hB η hη hk

end
end QuaternionicSymmetry.QuaternionicGeneralCubicPositivity
