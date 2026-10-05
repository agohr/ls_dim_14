import Mathlib.Tactic

/-!
Fourth polarization for the quartic square of a finite-dimensional Euclidean
quadratic form.  This file is a finite-sum algebra calculation only; it makes
no probabilistic or geometric claims.
-/

namespace QuaternionicSymmetry.FourthPolarization

variable {ι : Type*} [Fintype ι]


/-- The coordinate dot product on a finite function space. -/
def dot (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

@[simp] theorem dot_add_left (x y z : ι → ℝ) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, Finset.sum_add_distrib, add_mul]

@[simp] theorem dot_add_right (x y z : ι → ℝ) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, Finset.sum_add_distrib, mul_add]

@[simp] theorem dot_zero_left (x : ι → ℝ) : dot 0 x = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (x : ι → ℝ) : dot x 0 = 0 := by
  simp [dot]

theorem dot_comm (x y : ι → ℝ) : dot x y = dot y x := by
  simp [dot, mul_comm]

/-- The quartic function `q(v) = (dot v v)^2`. -/
def quartic (v : ι → ℝ) : ℝ := (dot v v) ^ 2

/-- The fourth polarization operator, with the standard 4/3/2/1 inclusion-exclusion signs. -/
def polarization (q : (ι → ℝ) → ℝ) (x y z w : ι → ℝ) : ℝ :=
    q (x + y + z + w)
      - (q (x + y + z) + q (x + y + w) + q (x + z + w) + q (y + z + w))
      + (q (x + y) + q (x + z) + q (x + w) + q (y + z) + q (y + w) + q (z + w))
      - (q x + q y + q z + q w)

/-- Fourth polarization of the quartic dot-product square. -/
theorem polarization_quartic (x y z w : ι → ℝ) :
    polarization quartic x y z w =
      8 * (dot x y * dot z w + dot x z * dot y w + dot x w * dot y z) := by
  simp only [polarization, quartic, dot_add_left, dot_add_right]
  simp only [dot_comm]
  ring

/-- The same identity with all dot products displayed as coordinate sums. -/
theorem polarization_quartic_sum (x y z w : ι → ℝ) :
    polarization quartic x y z w =
      8 * ((∑ i, x i * y i) * (∑ i, z i * w i) +
        (∑ i, x i * z i) * (∑ i, y i * w i) +
        (∑ i, x i * w i) * (∑ i, y i * z i)) := by
  simpa [dot] using polarization_quartic x y z w

/-- Scalar fourth polarization: the value is `24abcd`. -/
def scalarPolarization (a b c d : ℝ) : ℝ :=
    (a + b + c + d) ^ 4
      - ((a + b + c) ^ 4 + (a + b + d) ^ 4 + (a + c + d) ^ 4 + (b + c + d) ^ 4)
      + ((a + b) ^ 4 + (a + c) ^ 4 + (a + d) ^ 4 + (b + c) ^ 4 + (b + d) ^ 4 + (c + d) ^ 4)
      - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4)

theorem scalarPolarization_eq (a b c d : ℝ) :
    scalarPolarization a b c d = 24 * a * b * c * d := by
  simp only [scalarPolarization]
  ring

end QuaternionicSymmetry.FourthPolarization
