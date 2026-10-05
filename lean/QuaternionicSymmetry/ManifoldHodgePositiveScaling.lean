import QuaternionicSymmetry.ManifoldHodgeSquareApplication

/-! Positive rescaling preserves the generalized intersection inequality on
the actual de Rham classes. This keeps the choice of positive normalization
separate from the source theorem and from characteristic-class identification. -/

namespace QuaternionicSymmetry.ManifoldHodgeSquareApplication

open ManifoldEvenCharacteristicAlgebra ManifoldQuaternionicMetric
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M] in
private theorem of_cast {p q : ℕ} (h : p = q)
    (a : Grade (E := E) (M := M) p) :
    DirectSum.of (Grade (E := E) (M := M)) q (castGrade h a) =
      DirectSum.of _ p a := by
  cases h
  rfl

theorem real_constant_mul_of (c : ℝ) (m : ℕ)
    (a : Grade (E := E) (M := M) m) :
    DirectSum.of (Grade (E := E) (M := M)) 0 c * DirectSum.of _ m a =
      DirectSum.of _ m (c • a) := by
  rw [DirectSum.of_mul_of]
  cases m with
  | zero => rfl
  | succ m => exact of_cast (Nat.zero_add (m + 1)).symm (c • a)

theorem real_constant_mul (c : ℝ) (z : Total (E := E) (M := M)) :
    DirectSum.of (Grade (E := E) (M := M)) 0 c * z = c • z := by
  classical
  refine DirectSum.induction_on z ?_ ?_ ?_
  · simp
  · intro m a
    rw [real_constant_mul_of, DirectSum.of_smul]
  · intro a b ha hb
    rw [mul_add, ha, hb, smul_add]

theorem scaled_class_power (c : ℝ)
    (u : Grade (E := E) (M := M) 1) (j : ℕ) :
    (DirectSum.of (Grade (E := E) (M := M)) 1 (c • u)) ^ j =
      DirectSum.of _ 0 (c ^ j) * (DirectSum.of _ 1 u) ^ j := by
  rw [← real_constant_mul_of, mul_pow]
  have hc : (DirectSum.of (Grade (E := E) (M := M)) 0 c) ^ j =
      DirectSum.of _ 0 (c ^ j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [pow_succ, pow_succ, ih, real_constant_mul_of]
        rfl
  rw [hc]

variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem square_integral_scaling (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (c : ℝ) (u : Grade (E := E) (M := M) 1)
    (a : Total (E := E) (M := M)) (j : ℕ) :
    topIntegral Q k hdim (a ^ 2 * (DirectSum.of _ 1 (c • u)) ^ j) =
      c ^ j * topIntegral Q k hdim (a ^ 2 * (DirectSum.of _ 1 u) ^ j) := by
  rw [scaled_class_power, mul_left_comm, real_constant_mul, map_smul]
  rfl

theorem generalizedSquareNonnegative_smul (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (u : Grade (E := E) (M := M) 1)
    (hu : GeneralizedSquareNonnegative Q k hdim u)
    (c : ℝ) (hc : 0 ≤ c) :
    GeneralizedSquareNonnegative Q k hdim (c • u) := by
  intro m hm a
  rw [square_integral_scaling]
  exact mul_nonneg (pow_nonneg hc _) (hu m hm a)

theorem generalizedSquareNonnegative_smul_iff (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (u : Grade (E := E) (M := M) 1) (c : ℝ) (hc : 0 < c) :
    GeneralizedSquareNonnegative Q k hdim (c • u) ↔
      GeneralizedSquareNonnegative Q k hdim u := by
  constructor
  · intro h
    have h' := generalizedSquareNonnegative_smul Q k hdim (c • u) h
      c⁻¹ (inv_nonneg.mpr hc.le)
    simpa [smul_smul, hc.ne'] using h'
  · intro h
    exact generalizedSquareNonnegative_smul Q k hdim u h c hc.le

end
end QuaternionicSymmetry.ManifoldHodgeSquareApplication
