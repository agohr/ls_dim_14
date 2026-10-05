import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination

/-! Alternating the curvature action on any endomorphism vanishes by the
first Bianchi identity. This is the algebraic Bianchi identity used to
recover the quaternionic curvature coefficient forms. -/
namespace QuaternionicSymmetry.CurvatureBianchiAlternation

def action {E : Type*} (R : E → E → E → E → ℝ) (A : E → E)
    (x y z w : E) : ℝ := R x y (A z) w + R x y z (A w)

theorem alternation_zero {E : Type*} (R : E → E → E → E → ℝ)
    (hfirst : ∀ x y z w, R x y z w = -R y x z w)
    (hlast : ∀ x y z w, R x y z w = -R x y w z)
    (hB : ∀ x y z w, R x y z w + R y z x w + R z x y w = 0)
    (A : E → E) (x y z w : E) :
    action R A x y z w - action R A x z y w + action R A x w y z +
      action R A z w x y - action R A y w x z + action R A y z x w = 0 := by
  dsimp only [action]
  linear_combination
    hB x y z (A w) - hB x y w (A z) + hB x z w (A y) - hB y z w (A x) +
    -hfirst z x y (A w) + hfirst w x y (A z) - hfirst w x z (A y) +
    hfirst w y z (A x) +
    hlast x y (A z) w - hlast x z (A y) w + hlast x w (A y) z +
    hlast z w (A x) y - hlast y w (A x) z + hlast y z (A x) w

end QuaternionicSymmetry.CurvatureBianchiAlternation
