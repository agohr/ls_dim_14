import QuaternionicSymmetry.QuaternionicScalarTrace
import QuaternionicSymmetry.QuaternionicTraceOrthogonality

/-! The all-rank binomial trace formula for commuting quaternion-linear and
scalar quaternionic endomorphisms. This is the numerical precursor to the
higher tangent/standard Chern--Weil comparison. -/
namespace QuaternionicSymmetry.QuaternionicTangentEvenBinomial
open QuaternionicScalarTrace QuaternionicTraceOrthogonality
  LocalEndomorphismTrace
  VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  (S : QuaternionicStructure E) (a : Fin 3 → ℝ)

private def t : ℝ := ∑ i : Fin 3, a i * a i

omit [FiniteDimensional ℝ E] in
private theorem synth_square :
    (synth S a) ^ 2 = (-t a) • (1 : E →L[ℝ] E) := by
  have h := synth_anticommutator S a a
  change synth S a * synth S a + synth S a * synth S a =
    (-(2 * t a)) • (1 : E →L[ℝ] E) at h
  rw [pow_two]
  calc
    synth S a * synth S a =
        (1 / 2 : ℝ) • (synth S a * synth S a + synth S a * synth S a) := by module
    _ = (1 / 2 : ℝ) • ((-(2 * t a)) • (1 : E →L[ℝ] E)) := by rw [h]
    _ = (-t a) • (1 : E →L[ℝ] E) := by module

omit [FiniteDimensional ℝ E] in
private theorem synth_even_pow (j : ℕ) :
    (synth S a) ^ (2 * j) = (-t a) ^ j • (1 : E →L[ℝ] E) := by
  rw [pow_mul, synth_square, smul_pow]
  simp

omit [FiniteDimensional ℝ E] in
private theorem synth_odd_pow (j : ℕ) :
    (synth S a) ^ (2 * j + 1) = (-t a) ^ j • synth S a := by
  rw [pow_succ, synth_even_pow]
  simp

variable (P : E →L[ℝ] E)

theorem trace_even_mix (m j : ℕ) :
    traceCLM (P ^ m * (synth S a) ^ (2 * j)) =
      (-t a) ^ j * traceCLM (P ^ m) := by
  rw [synth_even_pow, mul_smul_comm, mul_one, map_smul]
  rfl

theorem trace_odd_mix (hP : ∀ b, P * synth S b = synth S b * P)
    (m j : ℕ) :
    traceCLM (P ^ m * (synth S a) ^ (2 * j + 1)) = 0 := by
  rw [synth_odd_pow, mul_smul_comm, map_smul]
  have hpow : ∀ b, P ^ m * synth S b = synth S b * P ^ m := by
    intro b
    exact (Commute.pow_left (hP b) m).eq
  rw [trace_mul_synth S (P ^ m) hpow a]
  simp

theorem trace_binomial_even (hP : ∀ b, P * synth S b = synth S b * P)
    (j : ℕ) :
    traceCLM ((P + synth S a) ^ (2 * j)) =
      ∑ m ∈ Finset.range (2 * j + 1),
        (if Even (2 * j - m) then
          (-t a) ^ ((2 * j - m) / 2) * traceCLM (P ^ m)
         else 0) * (Nat.choose (2 * j) m : ℝ) := by
  have hcomm : Commute P (synth S a) := hP a
  rw [hcomm.add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hnat (X : E →L[ℝ] E) (n : ℕ) :
      traceCLM (X * (n : E →L[ℝ] E)) =
        (n : ℝ) * traceCLM X := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, mul_add, map_add, ih]
        simp [add_mul]
  rw [hnat]
  rw [mul_comm (Nat.choose (2 * j) m : ℝ)]
  change traceCLM (P ^ m * (synth S a) ^ (2 * j - m)) *
    (Nat.choose (2 * j) m : ℝ) = _
  by_cases he : Even (2 * j - m)
  · simp only [if_pos he]
    obtain ⟨k, hk⟩ := he
    rw [hk]
    have hdiv : (k + k) / 2 = k := by omega
    rw [hdiv, show k + k = 2 * k by omega]
    rw [trace_even_mix S a P m k]
  · simp only [if_neg he]
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp he
    rw [hk]
    rw [trace_odd_mix S a P hP m k]

end
end QuaternionicSymmetry.QuaternionicTangentEvenBinomial
