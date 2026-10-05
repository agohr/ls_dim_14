import QuaternionicSymmetry.UnitaryHaarMeasure
import Mathlib.Data.Matrix.Block
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
The compact symplectic group as the subgroup of the finite complex unitary
group preserving the standard alternating matrix. Its probability measure is
constructed from Haar measure, and its trace moments are actual integrals.
No Harish--Chandra evaluation is assumed or proved in this module.
-/

namespace QuaternionicSymmetry.CompactSymplecticHaar

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The unitary stabilizer of a complex bilinear form. -/
def stabilizer (J : Matrix κ κ ℂ) : Subgroup (Matrix.unitaryGroup κ ℂ) where
  carrier := {u | (u : Matrix κ κ ℂ)ᵀ * J * (u : Matrix κ κ ℂ) = J}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ((u : Matrix κ κ ℂ) * (v : Matrix κ κ ℂ))ᵀ * J *
      ((u : Matrix κ κ ℂ) * (v : Matrix κ κ ℂ)) = J
    rw [Matrix.transpose_mul]
    calc
      _ = (v : Matrix κ κ ℂ)ᵀ *
          ((u : Matrix κ κ ℂ)ᵀ * J * (u : Matrix κ κ ℂ)) *
          (v : Matrix κ κ ℂ) := by simp only [mul_assoc]
      _ = J := by rw [hu]; exact hv
  inv_mem' := by
    intro u hu
    have hleft : (u : Matrix κ κ ℂ) * (↑u⁻¹ : Matrix κ κ ℂ) = 1 := by
      change ((u * u⁻¹ : Matrix.unitaryGroup κ ℂ) : Matrix κ κ ℂ) = 1
      simp
    have h := congrArg
      (fun A : Matrix κ κ ℂ => (↑u⁻¹ : Matrix κ κ ℂ)ᵀ * A *
        (↑u⁻¹ : Matrix κ κ ℂ)) hu
    dsimp only at h
    change (↑u⁻¹ : Matrix κ κ ℂ)ᵀ * J * (↑u⁻¹ : Matrix κ κ ℂ) = J
    rw [← h]
    calc
      _ = ((u : Matrix κ κ ℂ) * (↑u⁻¹ : Matrix κ κ ℂ))ᵀ * J *
          ((u : Matrix κ κ ℂ) * (↑u⁻¹ : Matrix κ κ ℂ)) := by
            rw [Matrix.transpose_mul]
            simp only [mul_assoc]
      _ = J := by rw [hleft]; simp

theorem isClosed_stabilizer (J : Matrix κ κ ℂ) :
    IsClosed (stabilizer J : Set (Matrix.unitaryGroup κ ℂ)) := by
  apply isClosed_eq _ continuous_const
  exact (continuous_subtype_val.matrix_transpose.mul continuous_const).mul
    continuous_subtype_val

instance stabilizer_compactSpace (J : Matrix κ κ ℂ) :
    CompactSpace (stabilizer J) :=
  isCompact_iff_compactSpace.mp (isClosed_stabilizer J).isCompact

instance stabilizer_measurableSpace (J : Matrix κ κ ℂ) :
    MeasurableSpace (stabilizer J) := borel (stabilizer J)

instance stabilizer_borelSpace (J : Matrix κ κ ℂ) : BorelSpace (stabilizer J) := ⟨rfl⟩

/-- Haar measure with total mass one on the compact unitary stabilizer. -/
def probability (J : Matrix κ κ ℂ) : Measure (stabilizer J) :=
  Measure.haarMeasure ⊤

instance probability_isProbabilityMeasure (J : Matrix κ κ ℂ) :
    IsProbabilityMeasure (probability J) where
  measure_univ := Measure.haarMeasure_self

instance probability_isHaarMeasure (J : Matrix κ κ ℂ) :
    Measure.IsHaarMeasure (probability J) := by
  unfold probability
  infer_instance

instance probability_isMulRightInvariant (J : Matrix κ κ ℂ) :
    Measure.IsMulRightInvariant (probability J) where
  map_mul_right_eq_self u := by
    have h := Measure.haarMeasure_unique
      (Measure.map (fun g : stabilizer J => g * u) (probability J))
      (⊤ : TopologicalSpace.PositiveCompacts (stabilizer J))
    simpa only [TopologicalSpace.PositiveCompacts.coe_top,
      Measure.map_apply (measurable_mul_const u) MeasurableSet.univ,
      Set.preimage_univ, measure_univ, one_smul] using h

instance probability_isInvInvariant (J : Matrix κ κ ℂ) :
    Measure.IsInvInvariant (probability J) where
  inv_eq_self := by
    have h := Measure.haarMeasure_unique (probability J).inv
      (⊤ : TopologicalSpace.PositiveCompacts (stabilizer J))
    simpa only [TopologicalSpace.PositiveCompacts.coe_top,
      Measure.inv_apply, Set.inv_univ, measure_univ, one_smul] using h

/-- Standard alternating form on complex dimension `2n`. -/
def standardJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem standardJ_transpose (n : ℕ) : (standardJ n)ᵀ = -standardJ n := by
  simp [standardJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

theorem standardJ_sq (n : ℕ) : standardJ n * standardJ n = -1 := by
  simp only [standardJ, Matrix.fromBlocks_multiply, mul_zero,
    mul_one, mul_neg, add_zero, zero_add]
  rw [← Matrix.fromBlocks_one (l := Fin n) (m := Fin n), Matrix.fromBlocks_neg]
  simp

/-- A concrete matrix model of the compact symplectic group `USp(2n)`. -/
abbrev Group (n : ℕ) := stabilizer (standardJ n)

/-- Half the real part of the complex trace of the conjugation pairing.
For skew-Hermitian test matrices the trace is real. -/
def halfTrace (J B X : Matrix κ κ ℂ) (g : stabilizer J) : ℝ :=
  (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) * X *
    (g.1 : Matrix κ κ ℂ)ᴴ)).re / 2

/-- The conjugation pairing of skew-Hermitian matrices is real. -/
theorem trace_pairing_im_zero (J B X : Matrix κ κ ℂ)
    (hB : Bᴴ = -B) (hX : Xᴴ = -X) (g : stabilizer J) :
    (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) * X *
      (g.1 : Matrix κ κ ℂ)ᴴ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (Matrix.trace _) = _
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hB, hX,
    mul_neg, neg_mul, neg_neg, ← mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [mul_assoc]

/-- The same real-trace statement for Hermitian contractions, as used by
the numerical spectral convention before continuation to curvature forms. -/
theorem trace_pairing_im_zero_of_hermitian (J B X : Matrix κ κ ℂ)
    (hB : Bᴴ = B) (hX : Xᴴ = X) (g : stabilizer J) :
    (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) * X *
      (g.1 : Matrix κ κ ℂ)ᴴ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (Matrix.trace _) = _
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hB, hX,
    ← mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [mul_assoc]

theorem continuous_halfTrace (J B X : Matrix κ κ ℂ) :
    Continuous (halfTrace J B X) := by
  have hc : Continuous (fun g : stabilizer J => (g.1 : Matrix κ κ ℂ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (Complex.continuous_re.comp
    (((continuous_const.mul hc).mul continuous_const).mul
      hc.matrix_conjTranspose).matrix_trace).div_const 2

theorem integrable_halfTrace_pow (J B X : Matrix κ κ ℂ) (k : ℕ) :
    Integrable (fun g => halfTrace J B X g ^ k) (probability J) := by
  exact ((continuous_halfTrace J B X).pow k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_exp_halfTrace (J B X : Matrix κ κ ℂ) (t : ℝ) :
    Integrable (fun g => Real.exp (t * halfTrace J B X g)) (probability J) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_halfTrace J B X))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Conversion from half trace to full real complex trace in every degree. -/
theorem fullTrace_integral_pow (J B X : Matrix κ κ ℂ) (k : ℕ) :
    (∫ g : stabilizer J,
      (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) * X *
        (g.1 : Matrix κ κ ℂ)ᴴ)).re ^ k ∂probability J) =
      2 ^ k * ∫ g, halfTrace J B X g ^ k ∂probability J := by
  have h (g : stabilizer J) :
      (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) * X *
        (g.1 : Matrix κ κ ℂ)ᴴ)).re = 2 * halfTrace J B X g := by
    unfold halfTrace
    ring
  simp_rw [h, mul_pow]
  exact integral_const_mul _ _

/-- An actual even orbital moment, before any spectral evaluation. -/
def evenMoment (J B X : Matrix κ κ ℂ) (k : ℕ) : ℝ :=
  ∫ g, halfTrace J B X g ^ (2 * k) ∂probability J

theorem evenMoment_zero (J B X : Matrix κ κ ℂ) : evenMoment J B X 0 = 1 := by
  simp [evenMoment]

theorem evenMoment_nonneg (J B X : Matrix κ κ ℂ) (k : ℕ) :
    0 ≤ evenMoment J B X k := by
  apply integral_nonneg
  intro g
  change 0 ≤ halfTrace J B X g ^ (2 * k)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- Matrix conjugation by an actual element of the compact group. -/
def conjugate (J : Matrix κ κ ℂ) (u : stabilizer J) (X : Matrix κ κ ℂ) :
    Matrix κ κ ℂ := (u.1 : Matrix κ κ ℂ) * X * (u.1 : Matrix κ κ ℂ)ᴴ

theorem halfTrace_conjugate_right (J B X : Matrix κ κ ℂ)
    (u g : stabilizer J) :
    halfTrace J B (conjugate J u X) g = halfTrace J B X (g * u) := by
  change (Matrix.trace (B * (g.1 : Matrix κ κ ℂ) *
      ((u.1 : Matrix κ κ ℂ) * X * (u.1 : Matrix κ κ ℂ)ᴴ) *
      (g.1 : Matrix κ κ ℂ)ᴴ)).re / 2 =
    (Matrix.trace (B * ((g.1 : Matrix κ κ ℂ) * (u.1 : Matrix κ κ ℂ)) * X *
      ((g.1 : Matrix κ κ ℂ) * (u.1 : Matrix κ κ ℂ))ᴴ)).re / 2
  simp only [Matrix.conjTranspose_mul, mul_assoc]

/-- Haar moments depend only on the compact symplectic conjugacy class of
the matrix being averaged. -/
theorem evenMoment_conjugate_right (J B X : Matrix κ κ ℂ)
    (u : stabilizer J) (k : ℕ) :
    evenMoment J B (conjugate J u X) k = evenMoment J B X k := by
  unfold evenMoment
  simp_rw [halfTrace_conjugate_right]
  exact integral_mul_right_eq_self (μ := probability J)
    (fun g : stabilizer J => halfTrace J B X g ^ (2 * k)) u

theorem halfTrace_conjugate_left (J B X : Matrix κ κ ℂ)
    (u g : stabilizer J) :
    halfTrace J (conjugate J u B) X g = halfTrace J B X (u⁻¹ * g) := by
  change (Matrix.trace ((u.1 : Matrix κ κ ℂ) * B * (u.1 : Matrix κ κ ℂ)ᴴ *
      (g.1 : Matrix κ κ ℂ) * X * (g.1 : Matrix κ κ ℂ)ᴴ)).re / 2 =
    (Matrix.trace (B * ((u.1 : Matrix κ κ ℂ)ᴴ * (g.1 : Matrix κ κ ℂ)) * X *
      ((u.1 : Matrix κ κ ℂ)ᴴ * (g.1 : Matrix κ κ ℂ))ᴴ)).re / 2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
  rw [Matrix.trace_mul_comm (u.1 : Matrix κ κ ℂ)]
  simp only [mul_assoc]

theorem evenMoment_conjugate_left (J B X : Matrix κ κ ℂ)
    (u : stabilizer J) (k : ℕ) :
    evenMoment J (conjugate J u B) X k = evenMoment J B X k := by
  unfold evenMoment
  simp_rw [halfTrace_conjugate_left]
  exact integral_mul_left_eq_self (μ := probability J)
    (fun g : stabilizer J => halfTrace J B X g ^ (2 * k)) u⁻¹

end
end QuaternionicSymmetry.CompactSymplecticHaar
