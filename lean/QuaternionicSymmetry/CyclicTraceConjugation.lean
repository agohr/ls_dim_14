import QuaternionicSymmetry.LocalEndomorphismTrace

/-! Cyclic trace powers are invariant under an honest inverse-pair
conjugation in a possibly noncommutative normed algebra. This is the
pointwise algebra needed when higher invariant trace forms are glued
across projective gauge charts. -/

namespace QuaternionicSymmetry.CyclicTraceConjugation

noncomputable section

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

omit [NormedAlgebra ℝ A] in
theorem conjugated_pow (g h a : A) (hgh : g * h = 1) (hhg : h * g = 1)
    (k : ℕ) : (h * a * g) ^ k = h * a ^ k * g := by
  induction k with
  | zero =>
      simpa only [pow_zero, mul_one] using hhg.symm
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc
        (h * a ^ k * g) * (h * a * g) =
            h * a ^ k * (g * h) * a * g := by noncomm_ring
        _ = h * a ^ k * 1 * a * g := by rw [hgh]
        _ = h * (a ^ k * a) * g := by simp only [mul_one]; noncomm_ring

theorem cyclic_trace_conjugated_pow
    (T : A →L[ℝ] B) (hT : ∀ a b : A, T (a * b) = T (b * a))
    (g h a : A) (hgh : g * h = 1) (hhg : h * g = 1) (k : ℕ) :
    T ((h * a * g) ^ k) = T (a ^ k) := by
  rw [conjugated_pow g h a hgh hhg k]
  calc
    T (h * a ^ k * g) = T ((a ^ k * g) * h) := by
      simpa only [mul_assoc] using hT h (a ^ k * g)
    _ = T (a ^ k) := by rw [mul_assoc, hgh, mul_one]

omit [NormedAlgebra ℝ A] in
/-- An entire ordered product transforms by one conjugation.  This also
handles products of distinct curvature coefficients, unlike `conjugated_pow`. -/
theorem conjugated_list_prod (g h : A) (hgh : g * h = 1) (hhg : h * g = 1)
    (as : List A) :
    (as.map (fun a => h * a * g)).prod = h * as.prod * g := by
  induction as with
  | nil =>
      simpa using hhg.symm
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      calc
        (h * a * g) * (h * as.prod * g) =
            h * a * (g * h) * as.prod * g := by noncomm_ring
        _ = h * (a * as.prod) * g := by rw [hgh]; simp only [mul_one]; noncomm_ring

/-- Cyclicity removes that conjugation after taking the trace. -/
theorem cyclic_trace_conjugated_list_prod
    (T : A →L[ℝ] B) (hT : ∀ a b : A, T (a * b) = T (b * a))
    (g h : A) (hgh : g * h = 1) (hhg : h * g = 1) (as : List A) :
    T ((as.map (fun a => h * a * g)).prod) = T as.prod := by
  rw [conjugated_list_prod g h hgh hhg as]
  calc
    T (h * as.prod * g) = T ((as.prod * g) * h) := by
      simpa only [mul_assoc] using hT h (as.prod * g)
    _ = T as.prod := by rw [mul_assoc, hgh, mul_one]

end
end QuaternionicSymmetry.CyclicTraceConjugation
