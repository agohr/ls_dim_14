import QuaternionicSymmetry.QuaternionicContinuousFundamental
import QuaternionicSymmetry.ExteriorContinuousPowers
import QuaternionicSymmetry.QuaternionicSpectralSign

/-! Nonvanishing of the actual repeated wedge of the continuous quaternionic
four-form, transported from the canonical exterior algebra proof. -/
namespace QuaternionicSymmetry.QuaternionicContinuousVolume

open Module QuaternionicFundamental ExteriorContinuousPairing ExteriorContinuousWedge
  ExteriorContinuousPowers QuaternionicContinuousFundamental
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem wedgePower_fundamental (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (n : ℕ) :
    wedgePower (fundamental Q) n =
      toContinuous (4*n) (powPower (fundamentalPower Q b) n) := by
  rw [toContinuous_powPower, toContinuous_fundamentalPower]

theorem wedgePower_fundamental_ne_zero (Q : QuaternionicStructure V) :
    wedgePower (fundamental Q) Q.quaternionicDimension ≠ 0 := by
  let b := Module.finBasis ℝ V
  rw [wedgePower_fundamental Q b]
  intro h
  have hz : powPower (fundamentalPower Q b) Q.quaternionicDimension = 0 :=
    toContinuous_injective _ (h.trans (toContinuous_zero _).symm)
  have he : form Q b ^ Q.quaternionicDimension = 0 := by
    apply Subtype.ext
    have hzv := congrArg (fun a : Power V (4 * Q.quaternionicDimension) => a.val) hz
    simpa only [powPower, fundamentalPower, ZeroMemClass.coe_zero, SubmonoidClass.coe_pow] using hzv
  apply QuaternionicSpectralSign.topForm_ne_zero Q b
  simp only [topForm, he, smul_zero]

end
end QuaternionicSymmetry.QuaternionicContinuousVolume
