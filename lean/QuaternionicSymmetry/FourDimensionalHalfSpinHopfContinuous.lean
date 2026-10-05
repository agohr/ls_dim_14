import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAction
import QuaternionicSymmetry.ComplexProjectiveHausdorff

/-! Continuity of the explicit Hopf map for the genuine quotient topology on
complex projective spinors and the existing Euclidean coefficient sphere.
No topology is transported from the target. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfContinuous

open scoped Quaternion Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinHopfProjectiveDescent
open ManifoldTwistorSphereBundle

noncomputable section

private abbrev NonzeroSpinor := {v : Spinor // v ≠ 0}

private theorem continuous_fromSpinor :
    Continuous (fun v : NonzeroSpinor => fromSpinor v.1) :=
  spinorQuaternionEquiv.toLinearMap.continuous_of_finiteDimensional.comp
    continuous_subtype_val

private theorem continuous_hopfRaw :
    Continuous (fun v : NonzeroSpinor => hopfRaw v.1) := by
  unfold hopfRaw
  exact ((continuous_fromSpinor.mul continuous_const).mul
    continuous_fromSpinor.star)

private theorem continuous_hopfQuaternion :
    Continuous (fun v : NonzeroSpinor => hopfQuaternion v.1 v.2) := by
  have hn : Continuous (fun v : NonzeroSpinor =>
      Quaternion.normSq (fromSpinor v.1)) :=
    Quaternion.continuous_normSq.comp continuous_fromSpinor
  have hn0 (v : NonzeroSpinor) :
      Quaternion.normSq (fromSpinor v.1) ≠ 0 := by
    apply (Quaternion.normSq_ne_zero).mpr
    intro hz
    apply v.2
    apply fromSpinor_injective
    simpa [fromSpinor] using hz
  have hc : Continuous (fun v : NonzeroSpinor =>
      (Quaternion.normSq (fromSpinor v.1))⁻¹ • hopfRaw v.1) :=
    (hn.inv₀ hn0).smul continuous_hopfRaw
  exact hc.congr fun v => (hopfQuaternion_eq_ratio v.1 v.2).symm

private theorem continuous_hopfSphere :
    Continuous (fun v : NonzeroSpinor => hopfSphere v.1 v.2) := by
  apply Continuous.subtype_mk
  have hI : Continuous (fun v : NonzeroSpinor =>
      (hopfQuaternion v.1 v.2).imI) :=
    Quaternion.continuous_imI.comp continuous_hopfQuaternion
  have hJ : Continuous (fun v : NonzeroSpinor =>
      (hopfQuaternion v.1 v.2).imJ) :=
    Quaternion.continuous_imJ.comp continuous_hopfQuaternion
  have hK : Continuous (fun v : NonzeroSpinor =>
      (hopfQuaternion v.1 v.2).imK) :=
    Quaternion.continuous_imK.comp continuous_hopfQuaternion
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [hopfSphere] using hI
  · simpa [hopfSphere] using hJ
  · simpa [hopfSphere] using hK

/-- The explicit projective Hopf map is continuous in the canonical
quotient topology of `ℙ ℂ ℂ²`. -/
theorem projectiveHopf_continuous : Continuous projectiveHopf := by
  apply (isQuotientMap_quotient_mk').continuous_iff.mpr
  change Continuous (projectiveHopf ∘ (Projectivization.mk' ℂ :
    NonzeroSpinor → ProjectiveSpinor))
  have heq : projectiveHopf ∘ (Projectivization.mk' ℂ :
      NonzeroSpinor → ProjectiveSpinor) =
      (fun v : NonzeroSpinor => hopfSphere v.1 v.2) := by
    funext v
    exact projectiveHopf_mk v.1 v.2
  rw [heq]
  exact continuous_hopfSphere

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfContinuous
