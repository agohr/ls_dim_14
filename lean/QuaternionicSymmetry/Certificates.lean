import Mathlib.Tactic

/-!
  Exact rational polynomial certificates from Chapter 10 of the textbook.

  This file concerns only the finite algebraic calculation.  It neither
  formalizes curvature positivity nor the geometric classification argument.

  `b₁`--`b₄` are the homogeneous terms of `log A-hat` after the split-root
  substitution `s_j = (-1)^j z_j / 2 - u^j`.  `a₀`--`a₄` are the first
  homogeneous terms of its exponential.  The definitions of `K₂`--`K₁₀`
  then convolve these terms with the (finite, relevant) Taylor coefficients
  of the virtual-character factor `Psi_n`.
-/

namespace QuaternionicSymmetry
namespace Certificates

variable {R : Type*} [Field R] [CharZero R]

/-- The first four homogeneous terms of `log A-hat`, with `u` retained. -/
def b₁ (n u z₁ : R) : R := -(n - 1) / 12 * u + z₁ / 24
def b₂ (n u z₁ z₂ : R) : R := (n - 7) / 1440 * u^2 - u * z₁ / 480 + z₂ / 2880
def b₃ (n u z₁ z₂ z₃ : R) : R :=
  -(n - 31) / 90720 * u^3 + u^2 * z₁ / 12096 - u * z₂ / 12096 + z₃ / 181440
def b₄ (n u z₁ z₂ z₃ z₄ : R) : R :=
  (n - 127) / 4838400 * u^4 - u^3 * z₁ / 345600 + u^2 * z₂ / 138240
    - u * z₃ / 345600 + z₄ / 9676800

/-- Terms of `exp (b₁ + b₂ + b₃ + b₄ + ...)`, through weight four. -/
def a₀ : R := 1
def a₁ (n u z₁ : R) : R := b₁ n u z₁
def a₂ (n u z₁ z₂ : R) : R := b₂ n u z₁ z₂ + b₁ n u z₁ ^ 2 / 2
def a₃ (n u z₁ z₂ z₃ : R) : R :=
  b₃ n u z₁ z₂ z₃ + b₁ n u z₁ * b₂ n u z₁ z₂ + b₁ n u z₁ ^ 3 / 6
def a₄ (n u z₁ z₂ z₃ z₄ : R) : R :=
  b₄ n u z₁ z₂ z₃ z₄ + b₁ n u z₁ * b₃ n u z₁ z₂ z₃ + b₂ n u z₁ z₂ ^ 2 / 2
    + b₁ n u z₁ ^ 2 * b₂ n u z₁ z₂ / 2 + b₁ n u z₁ ^ 4 / 24

set_option linter.unusedSectionVars false in
/-- The displayed terms satisfy the exponential coefficient recurrence. -/
theorem a₁_recurrence (n u z₁ : R) :
    a₁ n u z₁ = b₁ n u z₁ := rfl

theorem a₂_recurrence (n u z₁ z₂ : R) :
    2 * a₂ n u z₁ z₂ = b₁ n u z₁ * a₁ n u z₁ + 2 * b₂ n u z₁ z₂ := by
  simp only [a₂, a₁]
  ring

theorem a₃_recurrence (n u z₁ z₂ z₃ : R) :
    3 * a₃ n u z₁ z₂ z₃ = b₁ n u z₁ * a₂ n u z₁ z₂
      + 2 * b₂ n u z₁ z₂ * a₁ n u z₁ + 3 * b₃ n u z₁ z₂ z₃ := by
  simp only [a₃, a₂, a₁]
  ring

theorem a₄_recurrence (n u z₁ z₂ z₃ z₄ : R) :
    4 * a₄ n u z₁ z₂ z₃ z₄ = b₁ n u z₁ * a₃ n u z₁ z₂ z₃
      + 2 * b₂ n u z₁ z₂ * a₂ n u z₁ z₂ + 3 * b₃ n u z₁ z₂ z₃ * a₁ n u z₁
      + 4 * b₄ n u z₁ z₂ z₃ z₄ := by
  simp only [a₄, a₃, a₂, a₁]
  ring

/-- The algebraic generators used by the printed certificates.
Their geometric nonnegativity is a separate proof obligation. -/
def F₁ (z₁ : R) : R := z₁ / 24
def F₂ (z₁ z₂ : R) : R := z₁^2 / 1152 + z₂ / 2880
def F₃ (z₁ z₂ z₃ : R) : R := z₁^3 / 82944 + z₁ * z₂ / 69120 + z₃ / 181440
def F₄ (z₁ z₂ z₃ z₄ : R) : R :=
  z₁^4 / 7962624 + z₁^2 * z₂ / 3317760 + z₂^2 / 16588800
    + z₁ * z₃ / 4354560 + z₄ / 9676800

/-- The finite `F` generators satisfy the recurrence from Chapter 8. -/
theorem F₂_recurrence (z₁ z₂ : R) :
    2 * F₂ z₁ z₂ = (z₁ / 24) * F₁ z₁ + 2 * (z₂ / 2880) := by
  simp only [F₂, F₁]
  ring

theorem F₃_recurrence (z₁ z₂ z₃ : R) :
    3 * F₃ z₁ z₂ z₃ = (z₁ / 24) * F₂ z₁ z₂
      + 2 * (z₂ / 2880) * F₁ z₁ + 3 * (z₃ / 181440) := by
  simp only [F₃, F₂, F₁]
  ring

theorem F₄_recurrence (z₁ z₂ z₃ z₄ : R) :
    4 * F₄ z₁ z₂ z₃ z₄ = (z₁ / 24) * F₃ z₁ z₂ z₃
      + 2 * (z₂ / 2880) * F₂ z₁ z₂ + 3 * (z₃ / 181440) * F₁ z₁
      + 4 * (z₄ / 9676800) := by
  simp only [F₄, F₃, F₂, F₁]
  ring

def M₂₁ (r z₁ z₂ : R) : R := (z₁^2 + z₂) / (r * (r + 1))
def M₃₁ (r z₁ z₂ z₃ : R) : R :=
  (z₁^3 + 3 * z₁ * z₂ + 2 * z₃) / (r * (r + 1) * (r + 2))
def M₃₂ (r z₁ z₂ z₃ : R) : R :=
  4 * ((2 * r + 1) * z₁^3 + 3 * (r - 1) * z₁ * z₂ + (r - 4) * z₃)
    / (r * (r - 1) * (r + 1) * (r + 2))

/-- The finite density reconstructions, with the required Taylor data for `Psi_n`. -/
def K₂ (u _z₁ _z₂ _z₃ _z₄ : R) : R := 16 * u^2 * a₀
def K₃ (u z₁ _z₂ _z₃ _z₄ : R) : R :=
  32 * u^2 * a₁ 3 u z₁ + (112 / 3) * u^3 * a₀
def K₄ (u z₁ _z₂ _z₃ _z₄ : R) : R :=
  64 * u^3 * a₁ 4 u z₁ + 64 * u^4 * a₀
def K₅ (u z₁ z₂ _z₃ _z₄ : R) : R :=
  128 * u^3 * a₂ 5 u z₁ z₂ + 192 * u^4 * a₁ 5 u z₁ + (1936 / 15) * u^5 * a₀
def K₆ (u z₁ z₂ _z₃ _z₄ : R) : R :=
  256 * u^4 * a₂ 6 u z₁ z₂ + (1024 / 3) * u^5 * a₁ 6 u z₁ + (9728 / 45) * u^6 * a₀
def K₇ (u z₁ z₂ z₃ _z₄ : R) : R :=
  512 * u^4 * a₃ 7 u z₁ z₂ z₃ + (2816 / 3) * u^5 * a₂ 7 u z₁ z₂
    + (35776 / 45) * u^6 * a₁ 7 u z₁ + (79136 / 189) * u^7 * a₀
def K₈ (u z₁ z₂ z₃ _z₄ : R) : R :=
  1024 * u^5 * a₃ 8 u z₁ z₂ z₃ + (5120 / 3) * u^6 * a₂ 8 u z₁ z₂
    + (4096 / 3) * u^7 * a₁ 8 u z₁ + (44032 / 63) * u^8 * a₀
def K₉ (u z₁ z₂ z₃ z₄ : R) : R :=
  2048 * u^5 * a₄ 9 u z₁ z₂ z₃ z₄ + (13312 / 3) * u^6 * a₃ 9 u z₁ z₂ z₃
    + (13568 / 3) * u^7 * a₂ 9 u z₁ z₂ + (916096 / 315) * u^8 * a₁ 9 u z₁
    + (3777808 / 2835) * u^9 * a₀
def K₁₀ (u z₁ z₂ z₃ z₄ : R) : R :=
  4096 * u^6 * a₄ 10 u z₁ z₂ z₃ z₄ + 8192 * u^7 * a₃ 10 u z₁ z₂ z₃
    + (118784 / 15) * u^8 * a₂ 10 u z₁ z₂ + (4661248 / 945) * u^9 * a₁ 10 u z₁
    + (1503232 / 675) * u^10 * a₀

set_option linter.unusedSectionVars false in
theorem certificate₂ (u z₁ z₂ z₃ z₄ : R) : K₂ u z₁ z₂ z₃ z₄ = 16 * u^2 := by
  simp [K₂, a₀]

theorem certificate₃ (u z₁ z₂ z₃ z₄ : R) :
    K₃ u z₁ z₂ z₃ z₄ = 32 * u^3 + (4 / 3) * z₁ * u^2 := by
  simp only [K₃, a₀, a₁, b₁]
  ring

theorem certificate₄ (u z₁ z₂ z₃ z₄ : R) :
    K₄ u z₁ z₂ z₃ z₄ = 48 * u^4 + (8 / 3) * z₁ * u^3 := by
  simp only [K₄, a₀, a₁, b₁]
  ring

theorem certificate₅ (u z₁ z₂ z₃ z₄ : R) :
    K₅ u z₁ z₂ z₃ z₄ = 72 * u^5 + (268 / 45) * z₁ * u^4 + 128 * F₂ z₁ z₂ * u^3 := by
  simp only [K₅, a₂, a₁, a₀, b₂, b₁, F₂]
  ring

theorem certificate₆ (u z₁ z₂ z₃ z₄ : R) :
    K₆ u z₁ z₂ z₃ z₄ = 96 * u^6 + (416 / 45) * z₁ * u^5 + 256 * F₂ z₁ z₂ * u^4 := by
  simp only [K₆, a₂, a₁, a₀, b₂, b₁, F₂]
  ring

theorem certificate₇ (u z₁ z₂ z₃ z₄ : R) :
    K₇ u z₁ z₂ z₃ z₄ = 128 * u^7 + (104 / 7) * z₁ * u^6
      + ((50048 / 945) * M₂₁ 16 z₁ z₂ + (334 / 945) * z₁^2) * u^5
      + 512 * F₃ z₁ z₂ z₃ * u^4 := by
  simp only [K₇, a₃, a₂, a₁, a₀, b₃, b₂, b₁, M₂₁, F₃]
  ring

theorem certificate₈ (u z₁ z₂ z₃ z₄ : R) :
    K₈ u z₁ z₂ z₃ z₄ = 160 * u^8 + (6448 / 315) * z₁ * u^7
      + ((10792 / 105) * M₂₁ 18 z₁ z₂ + (542 / 945) * z₁^2) * u^6
      + 1024 * F₃ z₁ z₂ z₃ * u^5 := by
  simp only [K₈, a₃, a₂, a₁, a₀, b₃, b₂, b₁, M₂₁, F₃]
  ring

theorem certificate₉ (u z₁ z₂ z₃ z₄ : R) :
    K₉ u z₁ z₂ z₃ z₄ = 200 * u^9 + (45128 / 1575) * z₁ * u^8
      + ((8752 / 45) * M₂₁ 20 z₁ z₂ + (14704 / 14175) * z₁^2) * u^7
      + ((2992 / 405) * M₃₁ 20 z₁ z₂ z₃ + (2090 / 81) * M₃₂ 20 z₁ z₂ z₃
          + (239 / 28350) * z₁^3) * u^6
      + 2048 * F₄ z₁ z₂ z₃ z₄ * u^5 := by
  simp only [K₉, a₄, a₃, a₂, a₁, a₀, b₄, b₃, b₂, b₁, M₂₁, M₃₁, M₃₂, F₄]
  ring

theorem certificate₁₀ (u z₁ z₂ z₃ z₄ : R) :
    K₁₀ u z₁ z₂ z₃ z₄ = 240 * u^10 + (8288 / 225) * z₁ * u^9
      + ((1495736 / 4725) * M₂₁ 22 z₁ z₂ + (21278 / 14175) * z₁^2) * u^8
      + ((4048 / 4725) * M₃₁ 22 z₁ z₂ z₃ + (23276 / 405) * M₃₂ 22 z₁ z₂ z₃
          + (194 / 14175) * z₁^3) * u^7
      + 4096 * F₄ z₁ z₂ z₃ z₄ * u^6 := by
  simp only [K₁₀, a₄, a₃, a₂, a₁, a₀, b₄, b₃, b₂, b₁, M₂₁, M₃₁, M₃₂, F₄]
  ring

end Certificates
end QuaternionicSymmetry
