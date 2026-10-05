import QuaternionicSymmetry.QuaternionicExteriorCoordinates
import QuaternionicSymmetry.QuaternionicFundamental
import QuaternionicSymmetry.QuaternionicPencilPolynomial
import QuaternionicSymmetry.EvenFormsEquiv
import QuaternionicSymmetry.QuaternionicSpectralCoefficients
import QuaternionicSymmetry.QuaternionicTopForm
import QuaternionicSymmetry.QuaternionicEigenbasisDimension

/-! Transport of quaternionic block forms to the actual even exterior algebra
of the dual space through an orthonormal eigenbasis. -/

namespace QuaternionicSymmetry.QuaternionicEigenbasisTransport

open Module
open scoped BigOperators
open QuaternionicPencilPolynomial ExteriorCovectorTransport

noncomputable section

variable {β V : Type*} [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def transport (b : Basis (β × Fin 4) ℝ V) :
    Eev β →ₐ[ℝ] QuaternionicFundamental.E V :=
  EvenForms.map (covectorMap b)

theorem transport_injective (b : Basis (β × Fin 4) ℝ V) :
    Function.Injective (transport b) := by
  simpa only [transport, covectorMap_eq_dualBasis, covectorEquiv] using
    EvenForms.map_injective (covectorEquiv b)

theorem transport_theta (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) (vals : β → ℝ) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2)
    (heig : ∀ j, A (v j) = vals j • Q.I (v j)) :
    transport b.toBasis (theta vals) = HyperholomorphicExterior.evenForm b.toBasis A := by
  apply Subtype.ext
  have h := QuaternionicExteriorCoordinates.transport_alpha_sum_eq_form Q A hA vals v b hb heig
  change exteriorCovectorMap b.toBasis
      ((EvenForms.evenSubalgebra ℝ (QuaternionicBlocks.V β)).val (theta vals)) =
    (HyperholomorphicExterior.form b.toBasis A : ExteriorAlgebra ℝ (Module.Dual ℝ V))
  rw [theta, map_sum]
  simp only [map_smul]
  exact h

/-- Each coordinate invariant form transports to its intrinsic quaternionic
two-form in the eigenbasis. -/
theorem transport_omega (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) (i : Fin 3) :
    transport b.toBasis (omega i) = QuaternionicFundamental.omega Q b.toBasis i := by
  apply Subtype.ext
  fin_cases i
  · simpa [transport, omega, QuaternionicFundamental.omega] using
      QuaternionicExteriorCoordinates.transport_omegaI_sum_eq_form Q v b hb
  · simpa [transport, omega, QuaternionicFundamental.omega] using
      QuaternionicExteriorCoordinates.transport_omegaJ_sum_eq_form Q v b hb
  · simpa [transport, omega, QuaternionicFundamental.omega] using
      QuaternionicExteriorCoordinates.transport_omegaK_sum_eq_form Q v b hb

/-- The coordinate fundamental four-form transports to the intrinsic
quaternionic fundamental form. -/
theorem transport_fundamental (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    transport b.toBasis (QuaternionicSpectralCoefficients.fundamental : Eev β) =
      QuaternionicFundamental.form Q b.toBasis := by
  unfold QuaternionicSpectralCoefficients.fundamental QuaternionicFundamental.form
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_pow, transport_omega Q v b hb i]

/-- The coordinate volume is the normalized intrinsic top form. -/
theorem transport_volume (Q : QuaternionicStructure V) (v : β → V)
    (b : OrthonormalBasis (β × Fin 4) ℝ V)
    (hb : ∀ p, b p = Q.frame (v p.1) p.2) :
    transport b.toBasis (volume : Eev β) = QuaternionicFundamental.topForm Q b.toBasis := by
  rw [QuaternionicSpectralCoefficients.volume_eq_normalized_fundamental]
  rw [map_smul, map_pow, transport_fundamental Q v b hb,
    Q.card_eq_quaternionicDimension_of_orthonormalBasis b]
  rfl

end
end QuaternionicSymmetry.QuaternionicEigenbasisTransport
