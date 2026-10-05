import QuaternionicSymmetry.ComplexProjectiveActualConeTranslatedFractionChart
import QuaternionicSymmetry.ComplexProjectiveActualConeChartClassicalSpecialization
import Mathlib.RingTheory.Ideal.Maximal

/-! On a standard open, the canonical Mathlib Proj-to-Spec carrier of a
classical quotient-Proj point is precisely evaluation at its affine
coordinates, after the actual Away/chart quotient ring equivalence. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalCarrierEvaluation

open AlgebraicGeometry ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartLocus ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveActualConeClassicalTranslatedCarrier
open ComplexProjectiveActualConeTranslatedFractionChart
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeChartClassicalSpecialization
noncomputable section

variable {d : ℕ}

theorem chartPointEval_scalar (A : Set (Space d)) (i : Fin (d + 1))
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i) (c : ℂ) :
    chartPointEval A i w hw
      (algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) c) = c := by
  change chartPointEval A i w hw
    (Ideal.Quotient.mk _ (MvPolynomial.C c)) = c
  rw [chartPointEval_mk]
  simp

set_option maxRecDepth 2048 in
theorem classicalCarrier_eq_chartEvalKernel
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (x : A) (i : Fin (d + 1))
    (hi : x.1.rep i ≠ 0) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i)
    (hratio : ∀ k : Fin d,
      x.1.rep (i.succAbove k) = w k * x.1.rep i) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    let q : ProjectiveSpectrum (quotientPiece A) :=
      classicalPointToActualProjFixed A hA hNonempty x
    let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
        q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
      ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
    Ideal.comap (standardOpenAlgEquiv A hA hNonempty i).symm.toRingHom
      (ProjIsoSpecTopComponent.ToSpec.carrier qᵢ) =
      RingHom.ker (chartPointEval A i w hw) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  let q : ProjectiveSpectrum (quotientPiece A) :=
    classicalPointToActualProjFixed A hA hNonempty x
  let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
      q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
    ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
  let R := MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i
  let e := standardOpenAlgEquiv A hA hNonempty i
  let J : Ideal R := Ideal.comap e.symm.toRingHom
    (ProjIsoSpecTopComponent.ToSpec.carrier qᵢ)
  let ev : R →+* ℂ := chartPointEval A i w hw
  have hJprime : J.IsPrime :=
    (ProjIsoSpecTopComponent.ToSpec.isPrime_carrier qᵢ).comap e.symm.toRingHom
  have hrel (k : Fin d) :
      Ideal.Quotient.mk (chartVanishingIdeal A i)
        (MvPolynomial.X k - MvPolynomial.C (w k)) ∈ J := by
    change e.symm (Ideal.Quotient.mk (chartVanishingIdeal A i)
      (MvPolynomial.X k - MvPolynomial.C (w k))) ∈
      ProjIsoSpecTopComponent.ToSpec.carrier qᵢ
    have ht := (coordinateDifferenceFraction_mem_carrier_iff A hA hNonempty
      x i (i.succAbove k) hi (w k)).mpr (hratio k)
    have he := translatedFraction_chart A hA hNonempty i k (w k)
    rw [← he, e.symm_apply_apply]
    exact ht
  let φ : R →+* R ⧸ J := Ideal.Quotient.mk J
  let ψ : R →+* R ⧸ J := (algebraMap ℂ (R ⧸ J)).comp ev
  have hφψ : φ = ψ := by
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hpoly : φ.comp (Ideal.Quotient.mk (chartVanishingIdeal A i)) =
        ψ.comp (Ideal.Quotient.mk (chartVanishingIdeal A i)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change (algebraMap ℂ (R ⧸ J)) c =
          (algebraMap ℂ (R ⧸ J))
            (chartPointEval A i w hw
              (Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c)))
        rw [chartPointEval_mk]
        simp
      · intro k
        have hz : φ (Ideal.Quotient.mk (chartVanishingIdeal A i)
            (MvPolynomial.X k - MvPolynomial.C (w k))) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (hrel k)
        have hC : φ (Ideal.Quotient.mk (chartVanishingIdeal A i)
            (MvPolynomial.C (w k))) = algebraMap ℂ (R ⧸ J) (w k) := rfl
        have hk : φ (Ideal.Quotient.mk (chartVanishingIdeal A i)
            (MvPolynomial.X k)) = algebraMap ℂ (R ⧸ J) (w k) := by
          have hz' : φ (Ideal.Quotient.mk (chartVanishingIdeal A i)
              (MvPolynomial.X k)) - φ (Ideal.Quotient.mk (chartVanishingIdeal A i)
                (MvPolynomial.C (w k))) = 0 := by
            simpa only [map_sub] using hz
          exact hC ▸ sub_eq_zero.mp hz'
        change φ (Ideal.Quotient.mk (chartVanishingIdeal A i)
            (MvPolynomial.X k)) =
          algebraMap ℂ (R ⧸ J)
            (chartPointEval A i w hw
              (Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.X k)))
        rw [chartPointEval_mk]
        simpa using hk
    exact congrArg (fun f : MvPolynomial (Fin d) ℂ →+* R ⧸ J => f p) hpoly
  have hle : RingHom.ker ev ≤ J := by
    intro a ha
    have hz : φ a = 0 := by
      rw [hφψ]
      simp [ψ, (RingHom.mem_ker).mp ha]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hevSurj : Function.Surjective ev := by
    intro c
    exact ⟨algebraMap ℂ R c, chartPointEval_scalar A i w hw c⟩
  have hmax : (RingHom.ker ev).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective ev hevSurj
  exact (hmax.eq_of_le hJprime.ne_top hle).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalCarrierEvaluation
