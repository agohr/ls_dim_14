import Mathlib.Tactic

/-! Pair-interchange symmetry follows algebraically from the first Bianchi
identity and skewness in both argument pairs. -/
namespace QuaternionicSymmetry.AlgebraicRiemannPairSymmetry

theorem pair_symmetry {E : Type*} (R : E → E → E → E → ℝ)
    (h12 : ∀ a b c d, R a b c d = -R b a c d)
    (h34 : ∀ a b c d, R a b c d = -R a b d c)
    (hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (u v w z : E) : R u v w z = R w z u v := by
  have hB0 := hB u v w z
  have hS0 := h12 u v w z
  have hT0 := h34 u v w z
  have hB1 := hB u v z w
  have hS1 := h12 u v z w
  have hT1 := h34 u v z w
  have hB2 := hB u w v z
  have hS2 := h12 u w v z
  have hT2 := h34 u w v z
  have hB3 := hB u w z v
  have hS3 := h12 u w z v
  have hT3 := h34 u w z v
  have hB4 := hB u z v w
  have hS4 := h12 u z v w
  have hT4 := h34 u z v w
  have hB5 := hB u z w v
  have hS5 := h12 u z w v
  have hT5 := h34 u z w v
  have hB6 := hB v u w z
  have hS6 := h12 v u w z
  have hT6 := h34 v u w z
  have hB7 := hB v u z w
  have hS7 := h12 v u z w
  have hT7 := h34 v u z w
  have hB8 := hB v w u z
  have hS8 := h12 v w u z
  have hT8 := h34 v w u z
  have hB9 := hB v w z u
  have hS9 := h12 v w z u
  have hT9 := h34 v w z u
  have hB10 := hB v z u w
  have hS10 := h12 v z u w
  have hT10 := h34 v z u w
  have hB11 := hB v z w u
  have hS11 := h12 v z w u
  have hT11 := h34 v z w u
  have hB12 := hB w u v z
  have hS12 := h12 w u v z
  have hT12 := h34 w u v z
  have hB13 := hB w u z v
  have hS13 := h12 w u z v
  have hT13 := h34 w u z v
  have hB14 := hB w v u z
  have hS14 := h12 w v u z
  have hT14 := h34 w v u z
  have hB15 := hB w v z u
  have hS15 := h12 w v z u
  have hT15 := h34 w v z u
  have hB16 := hB w z u v
  have hS16 := h12 w z u v
  have hT16 := h34 w z u v
  have hB17 := hB w z v u
  have hS17 := h12 w z v u
  have hT17 := h34 w z v u
  have hB18 := hB z u v w
  have hS18 := h12 z u v w
  have hT18 := h34 z u v w
  have hB19 := hB z u w v
  have hS19 := h12 z u w v
  have hT19 := h34 z u w v
  have hB20 := hB z v u w
  have hS20 := h12 z v u w
  have hT20 := h34 z v u w
  have hB21 := hB z v w u
  have hS21 := h12 z v w u
  have hT21 := h34 z v w u
  have hB22 := hB z w u v
  have hS22 := h12 z w u v
  have hT22 := h34 z w u v
  have hB23 := hB z w v u
  have hS23 := h12 z w v u
  have hT23 := h34 z w v u
  linarith only [hB0, hS0, hT0, hB1, hS1, hT1, hB2, hS2, hT2, hB3, hS3, hT3, hB4, hS4, hT4, hB5, hS5, hT5, hB6, hS6, hT6, hB7, hS7, hT7, hB8, hS8, hT8, hB9, hS9, hT9, hB10, hS10, hT10, hB11, hS11, hT11, hB12, hS12, hT12, hB13, hS13, hT13, hB14, hS14, hT14, hB15, hS15, hT15, hB16, hS16, hT16, hB17, hS17, hT17, hB18, hS18, hT18, hB19, hS19, hT19, hB20, hS20, hT20, hB21, hS21, hT21, hB22, hS22, hT22, hB23, hS23, hT23]

end QuaternionicSymmetry.AlgebraicRiemannPairSymmetry
