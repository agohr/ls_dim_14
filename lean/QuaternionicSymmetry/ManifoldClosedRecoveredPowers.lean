import QuaternionicSymmetry.ManifoldEvenClosedAlgebra
import QuaternionicSymmetry.QuaternionicTangentRootConversion

/-! Homogeneous closed representatives of the finite triangular root recovery.
The inputs are actual closed forms, with normalized tangent trace grades. -/
namespace QuaternionicSymmetry.ManifoldClosedRecoveredPowers
open ManifoldEvenClosedAlgebra QuaternionicTangentRootConversion
open scoped Manifold ContDiff
noncomputable section
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 def quarterUTotal (u : Grade E M 1) (_t : ∀ j : ℕ, Grade E M (j+1)) :
    Total (E := E) (M := M) := DirectSum.of _ 1 u

def normalizedTangentHalfTrace (_u : Grade E M 1) (t : ∀ j : ℕ, Grade E M (j+1))
    (qdim : ℕ) : ℕ → Total (E := E) (M := M)
  | 0 => rationalConstants (2*qdim)
  | j+1 => DirectSum.of _ (j+1) (t j)

local instance : CommRing (Total (E := E) (M := M)) := inferInstance
local instance : AddCommGroup (Total (E := E) (M := M)) :=
  (inferInstance : CommRing (Total (E := E) (M := M))).toAddCommGroup
local instance : Algebra ℚ (Total (E := E) (M := M)) := rationalConstants.toAlgebra

variable (u : Grade E M 1) (t : ∀ j : ℕ, Grade E M (j+1))

def candidatePower (qdim : ℕ) (j : Fin 7) : Total (E := E) (M := M) :=
  recoveredStandardPower qdim (quarterUTotal u t) (normalizedTangentHalfTrace u t qdim) j

private def PureGrade (k : ℕ) (z : Total (E := E) (M := M)) : Prop :=
  ∃ a : Grade (E := E) (M := M) k,
    z = DirectSum.of (Grade (E := E) (M := M)) k a

private theorem pure_add {k : ℕ} {z w : Total (E := E) (M := M)}
    (hz : PureGrade k z) (hw : PureGrade k w) : PureGrade k (z + w) := by
  rcases hz with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  exact ⟨a + b, by simp⟩

private theorem pure_neg {k : ℕ} {z : Total (E := E) (M := M)}
    (hz : PureGrade k z) : PureGrade k (-z) := by
  rcases hz with ⟨a, rfl⟩
  exact ⟨-a, by simp⟩

private theorem pure_sub {k : ℕ} {z w : Total (E := E) (M := M)}
    (hz : PureGrade k z) (hw : PureGrade k w) : PureGrade k (z - w) := by
  simpa only [sub_eq_add_neg] using pure_add hz (pure_neg hw)

private theorem pure_mul {j k : ℕ} {z w : Total (E := E) (M := M)}
    (hz : PureGrade j z) (hw : PureGrade k w) : PureGrade (j + k) (z * w) := by
  rcases hz with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  exact ⟨gradeMul j k a b, DirectSum.of_mul_of a b⟩

private theorem pure_pow {j : ℕ} {z : Total (E := E) (M := M)}
    (hz : PureGrade j z) (k : ℕ) : PureGrade (k * j) (z ^ k) := by
  rcases hz with ⟨a, rfl⟩
  refine ⟨GradedMonoid.GMonoid.gnpow k a, ?_⟩
  simpa only [nsmul_eq_mul] using
    (DirectSum.ofPow (Grade (E := E) (M := M)) a k)

private theorem pure_u : PureGrade 1 (quarterUTotal u t) :=
  ⟨u, rfl⟩

private theorem pure_tangent (qdim j : ℕ) :
    PureGrade (j + 1) (normalizedTangentHalfTrace u t qdim (j + 1)) :=
  ⟨t j, rfl⟩

private theorem pure_rational (q : ℚ) :
    PureGrade 0 (rationalConstants (E := E) (M := M) q) :=
  ⟨(q : ℝ), rfl⟩

private theorem pure_nat (n : ℕ) :
    PureGrade 0 (n : Total (E := E) (M := M)) := by
  simpa only [map_natCast] using pure_rational (E := E) (M := M) (n : ℚ)

private theorem pure_half :
    PureGrade 0 (half (R := Total (E := E) (M := M))) := by
  dsimp [half]
  change PureGrade 0 ((rationalConstants (E := E) (M := M)) (1 / 2))
  exact pure_rational (E := E) (M := M) (1 / 2)

private theorem pure_u_pow (j : ℕ) :
    PureGrade j ((quarterUTotal u t) ^ j) := by
  simpa only [Nat.mul_one] using pure_pow (pure_u u t) j

private theorem pure_half_tangent (qdim j : ℕ) :
    PureGrade (j + 1)
      (half * normalizedTangentHalfTrace u t qdim (j + 1)) := by
  simpa only [Nat.zero_add] using
    pure_mul (pure_half (E := E) (M := M)) (pure_tangent u t qdim j)

private theorem pure_nat_u_pow (qdim j : ℕ) :
    PureGrade j
      ((qdim : Total (E := E) (M := M)) * (quarterUTotal u t) ^ j) := by
  simpa only [Nat.zero_add] using
    pure_mul (pure_nat (E := E) (M := M) qdim) (pure_u_pow u t j)

private theorem pure_coefficient_term (c a b : ℕ)
    (q : Total (E := E) (M := M)) (hq : PureGrade b q) :
    PureGrade (a + b)
      ((c : Total (E := E) (M := M)) * (quarterUTotal u t) ^ a * q) := by
  have hcu : PureGrade a
      ((c : Total (E := E) (M := M)) * (quarterUTotal u t) ^ a) := by
    simpa only [Nat.zero_add] using
      pure_mul (pure_nat (E := E) (M := M) c) (pure_u_pow u t a)
  exact pure_mul hcu hq

private theorem pure_recoveredQ1 (qdim : ℕ) :
    PureGrade 1 (recoveredQ1 qdim (quarterUTotal u t)
      (normalizedTangentHalfTrace u t qdim)) := by
  unfold recoveredQ1
  simpa using pure_sub (pure_half_tangent u t qdim 0)
    (pure_nat_u_pow u t qdim 1)

private theorem pure_recoveredQ2 (qdim : ℕ) :
    PureGrade 2 (recoveredQ2 qdim (quarterUTotal u t)
      (normalizedTangentHalfTrace u t qdim)) := by
  unfold recoveredQ2
  have h1 := pure_sub (pure_half_tangent u t qdim 1)
    (pure_nat_u_pow u t qdim 2)
  have h2 := pure_coefficient_term u t 6 1 1 _ (pure_recoveredQ1 u t qdim)
  simp only [Nat.cast_ofNat] at h2
  have hf := pure_sub h1 h2
  convert hf using 1

private theorem pure_recoveredQ3 (qdim : ℕ) :
    PureGrade 3 (recoveredQ3 qdim (quarterUTotal u t)
      (normalizedTangentHalfTrace u t qdim)) := by
  unfold recoveredQ3
  have h0 := pure_sub (pure_half_tangent u t qdim 2)
    (pure_nat_u_pow u t qdim 3)
  have ht1 : PureGrade 3
      ((15 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 2 *
        recoveredQ1 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 15 2 1 _
      (pure_recoveredQ1 u t qdim)
  have ht2 : PureGrade 3
      ((15 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 1 *
        recoveredQ2 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 15 1 2 _
      (pure_recoveredQ2 u t qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  convert hs2 using 1

private theorem pure_recoveredQ4 (qdim : ℕ) :
    PureGrade 4 (recoveredQ4 qdim (quarterUTotal u t)
      (normalizedTangentHalfTrace u t qdim)) := by
  unfold recoveredQ4
  have h0 := pure_sub (pure_half_tangent u t qdim 3)
    (pure_nat_u_pow u t qdim 4)
  have ht1 : PureGrade 4
      ((28 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 3 *
        recoveredQ1 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 28 3 1 _
      (pure_recoveredQ1 u t qdim)
  have ht2 : PureGrade 4
      ((70 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 2 *
        recoveredQ2 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 70 2 2 _
      (pure_recoveredQ2 u t qdim)
  have ht3 : PureGrade 4
      ((28 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 1 *
        recoveredQ3 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 28 1 3 _
      (pure_recoveredQ3 u t qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  have hs3 := pure_sub hs2 ht3
  convert hs3 using 1

private theorem pure_recoveredQ5 (qdim : ℕ) :
    PureGrade 5 (recoveredQ5 qdim (quarterUTotal u t)
      (normalizedTangentHalfTrace u t qdim)) := by
  unfold recoveredQ5
  have h0 := pure_sub (pure_half_tangent u t qdim 4)
    (pure_nat_u_pow u t qdim 5)
  have ht1 : PureGrade 5
      ((45 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 4 *
        recoveredQ1 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 45 4 1 _
      (pure_recoveredQ1 u t qdim)
  have ht2 : PureGrade 5
      ((210 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 3 *
        recoveredQ2 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 210 3 2 _
      (pure_recoveredQ2 u t qdim)
  have ht3 : PureGrade 5
      ((210 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 2 *
        recoveredQ3 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 210 2 3 _
      (pure_recoveredQ3 u t qdim)
  have ht4 : PureGrade 5
      ((45 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 1 *
        recoveredQ4 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 45 1 4 _
      (pure_recoveredQ4 u t qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  have hs3 := pure_sub hs2 ht3
  have hs4 := pure_sub hs3 ht4
  convert hs4 using 1

private theorem pure_recoveredQ6 (qdim : ℕ) :
    PureGrade 6 (recoveredQ6 qdim (quarterUTotal u t)
      (normalizedTangentHalfTrace u t qdim)) := by
  unfold recoveredQ6
  have h0 := pure_sub (pure_half_tangent u t qdim 5)
    (pure_nat_u_pow u t qdim 6)
  have ht1 : PureGrade 6
      ((66 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 5 *
        recoveredQ1 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 66 5 1 _
      (pure_recoveredQ1 u t qdim)
  have ht2 : PureGrade 6
      ((495 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 4 *
        recoveredQ2 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 495 4 2 _
      (pure_recoveredQ2 u t qdim)
  have ht3 : PureGrade 6
      ((924 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 3 *
        recoveredQ3 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 924 3 3 _
      (pure_recoveredQ3 u t qdim)
  have ht4 : PureGrade 6
      ((495 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 2 *
        recoveredQ4 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 495 2 4 _
      (pure_recoveredQ4 u t qdim)
  have ht5 : PureGrade 6
      ((66 : Total (E := E) (M := M)) * (quarterUTotal u t) ^ 1 *
        recoveredQ5 qdim (quarterUTotal u t)
          (normalizedTangentHalfTrace u t qdim)) := by
    simpa using pure_coefficient_term u t 66 1 5 _
      (pure_recoveredQ5 u t qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  have hs3 := pure_sub hs2 ht3
  have hs4 := pure_sub hs3 ht4
  have hs5 := pure_sub hs4 ht5
  convert hs5 using 1

private theorem pure_recoveredSymplecticPowers (qdim : ℕ) (j : Fin 7) :
    PureGrade j.val
      (recoveredSymplecticPowers qdim (quarterUTotal u t)
        (normalizedTangentHalfTrace u t qdim) j) := by
  fin_cases j
  · exact pure_nat (E := E) (M := M) qdim
  · exact pure_recoveredQ1 u t qdim
  · exact pure_recoveredQ2 u t qdim
  · exact pure_recoveredQ3 u t qdim
  · exact pure_recoveredQ4 u t qdim
  · exact pure_recoveredQ5 u t qdim
  · exact pure_recoveredQ6 u t qdim

private theorem pure_sign (j : ℕ) :
    PureGrade 0 ((-1 : Total (E := E) (M := M)) ^ j) := by
  have hneg : PureGrade 0 (-1 : Total (E := E) (M := M)) := by
    simpa using pure_neg (pure_nat (E := E) (M := M) 1)
  simpa only [Nat.mul_zero] using pure_pow hneg j

/-- Every recovered closed standard power sum through weight six lies
entirely in its expected form degree `4j`. -/
theorem candidatePower_pure_grade (qdim : ℕ) (j : Fin 7) :
    PureGrade j.val (candidatePower u t qdim j) := by
  unfold candidatePower recoveredStandardPower
  have hsum := pure_add (pure_recoveredSymplecticPowers u t qdim j)
    (pure_u_pow u t j.val)
  simpa only [Nat.zero_add] using
    pure_mul (pure_sign (E := E) (M := M) j.val) hsum

/-- The homogeneous closed form recovered from the normalized curvature traces. -/
noncomputable def candidatePowerClass (qdim : ℕ) (j : Fin 7) :
    Grade (E := E) (M := M) j.val :=
  (candidatePower_pure_grade u t qdim j).choose

theorem candidatePower_eq_of_class (qdim : ℕ) (j : Fin 7) :
    candidatePower u t qdim j =
      DirectSum.of (Grade (E := E) (M := M)) j.val
        (candidatePowerClass u t qdim j) :=
  (candidatePower_pure_grade u t qdim j).choose_spec


end
end QuaternionicSymmetry.ManifoldClosedRecoveredPowers
