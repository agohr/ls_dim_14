import QuaternionicSymmetry.CharacteristicMomentDictionary
import QuaternionicSymmetry.AlgebraCertificates
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-!
# The compact characteristic-coordinate identities from Chapter 6

These are equalities of universal rational polynomials. `c₂`, `c₄`, and
`c₆` are formal Chern variables, and `u` is a separate formal variable.
No characteristic class, integrated number, or positivity claim is made.
-/

namespace QuaternionicSymmetry.CompactCharacteristicDictionary

open MvPolynomial
noncomputable section

/-- The displayed inverse cubic dictionary, including its exact rational
normalization. -/
theorem mu3_two_traditional (r : ℚ) (hr : 2 < r) :
    CharacteristicMomentDictionary.m3Two r =
      C (16 / (r * (r - 1) * (r + 1))) *
        (CharacteristicMomentDictionary.S3 -
          C (3 / 2) * CharacteristicMomentDictionary.C3 -
          C ((r + 20) / (2 * (r + 2))) * CharacteristicMomentDictionary.H3) := by
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  have hpr1 : r + 1 ≠ 0 := by linarith
  have hpr2 : r + 2 ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [CharacteristicMomentDictionary.m3Two,
    CharacteristicMomentDictionary.S3, CharacteristicMomentDictionary.C3,
    CharacteristicMomentDictionary.H3, CharacteristicMomentDictionary.z1,
    CharacteristicMomentDictionary.z2, CharacteristicMomentDictionary.z3,
    CharacteristicMomentDictionary.c2, CharacteristicMomentDictionary.c4,
    CharacteristicMomentDictionary.c6]
  field_simp
  ring

abbrev P := MvPolynomial (Fin 4) ℚ
def u : P := X 0
def c2 : P := X 1
def c4 : P := X 2
def c6 : P := X 3

/-- Preserve the existing three-variable characteristic dictionary under a
polynomial substitution into the full ring with `u`. -/
def includeChern : CharacteristicMomentDictionary.P →ₐ[ℚ] P :=
  aeval ![c2, c4, c6]

def C1 : P := c2
def C2 : P := c2 ^ 2
def H2 : P := 3 * c2 ^ 2 - 2 * c4
def S3 : P := 10 * c2 ^ 3 - 9 * c2 * c4 + 2 * c6
def z1 : P := 2 * c2
def z2 : P := 2 * c2 ^ 2 - 4 * c4
def z3 : P := 2 * c2 ^ 3 - 6 * c2 * c4 + 6 * c6

theorem same_dictionary :
    C1 = includeChern CharacteristicMomentDictionary.C1 ∧
    C2 = includeChern CharacteristicMomentDictionary.C2 ∧
    H2 = includeChern CharacteristicMomentDictionary.H2 ∧
    S3 = includeChern CharacteristicMomentDictionary.S3 ∧
    z1 = includeChern CharacteristicMomentDictionary.z1 ∧
    z2 = includeChern CharacteristicMomentDictionary.z2 ∧
    z3 = includeChern CharacteristicMomentDictionary.z3 := by
  simp [C1, C2, H2, S3, z1, z2, z3, includeChern,
    CharacteristicMomentDictionary.C1, CharacteristicMomentDictionary.C2,
    CharacteristicMomentDictionary.H2, CharacteristicMomentDictionary.S3,
    CharacteristicMomentDictionary.z1, CharacteristicMomentDictionary.z2,
    CharacteristicMomentDictionary.z3, CharacteristicMomentDictionary.c2,
    CharacteristicMomentDictionary.c4, CharacteristicMomentDictionary.c6]
  simp only [map_ofNat]
  norm_num

/-- The old density interface, after the Newton substitution into formal
Chern variables. The unused fourth power sum is set to zero; degrees 5–8 do
not depend on it. -/
def density5 : P := AlgebraCertificates.evaluate u z1 z2 z3 0 AlgebraCertificates.K₅
def density6 : P := AlgebraCertificates.evaluate u z1 z2 z3 0 AlgebraCertificates.K₆
def density7 : P := AlgebraCertificates.evaluate u z1 z2 z3 0 AlgebraCertificates.K₇
def density8 : P := AlgebraCertificates.evaluate u z1 z2 z3 0 AlgebraCertificates.K₈

theorem compact_five :
    45 * density5 =
      3240 * u ^ 5 + 536 * C1 * u ^ 4 +
      12 * C2 * u ^ 3 + 4 * H2 * u ^ 3 := by
  unfold density5
  rw [AlgebraCertificates.polynomial_certificate₅]
  apply MvPolynomial.funext
  intro v
  simp [AlgebraCertificates.evaluate, AlgebraCertificates.RHS₅,
    AlgebraCertificates.F₂, AlgebraCertificates.c,
    AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    C1, C2, H2, z1, z2, u, c2, c4]
  ring

theorem compact_six :
    45 * density6 =
      4320 * u ^ 6 + 832 * C1 * u ^ 5 +
      24 * C2 * u ^ 4 + 8 * H2 * u ^ 4 := by
  unfold density6
  rw [AlgebraCertificates.polynomial_certificate₆]
  apply MvPolynomial.funext
  intro v
  simp [AlgebraCertificates.evaluate, AlgebraCertificates.RHS₆,
    AlgebraCertificates.F₂, AlgebraCertificates.c,
    AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    C1, C2, H2, z1, z2, u, c2, c4]
  ring

theorem compact_seven :
    945 * density7 =
      120960 * u ^ 7 + 28080 * C1 * u ^ 6 +
      1336 * C2 * u ^ 5 + 368 * H2 * u ^ 5 + 8 * S3 * u ^ 4 := by
  unfold density7
  rw [AlgebraCertificates.polynomial_certificate₇]
  apply MvPolynomial.funext
  intro v
  simp [AlgebraCertificates.evaluate, AlgebraCertificates.RHS₇,
    AlgebraCertificates.F₃, AlgebraCertificates.M₂₁,
    AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃,
    C1, C2, H2, S3, z1, z2, z3, u, c2, c4, c6]
  ring

theorem compact_eight :
    4725 * density8 =
      756000 * u ^ 8 + 193440 * C1 * u ^ 7 +
      10840 * C2 * u ^ 6 + 2840 * H2 * u ^ 6 + 80 * S3 * u ^ 5 := by
  unfold density8
  rw [AlgebraCertificates.polynomial_certificate₈]
  apply MvPolynomial.funext
  intro v
  simp [AlgebraCertificates.evaluate, AlgebraCertificates.RHS₈,
    AlgebraCertificates.F₃, AlgebraCertificates.M₂₁,
    AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃,
    C1, C2, H2, S3, z1, z2, z3, u, c2, c4, c6]
  ring

end
end QuaternionicSymmetry.CompactCharacteristicDictionary
