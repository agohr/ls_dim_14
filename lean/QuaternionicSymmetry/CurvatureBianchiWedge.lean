import QuaternionicSymmetry.CurvatureBianchiAlternation
import QuaternionicSymmetry.QuaternionicBianchiWedgeEight

/-! The first Bianchi identity implies the scalar-component wedge identities
for a curvature tensor normalizing the quaternionic structure. -/
namespace QuaternionicSymmetry.CurvatureBianchiWedge
open CurvatureBianchiAlternation QuaternionicBianchiWedgeEight

theorem wedge_eq_of_action {E : Type*} (R : E → E → E → E → ℝ)
    (hfirst : ∀ x y z w, R x y z w = -R y x z w)
    (hlast : ∀ x y z w, R x y z w = -R x y w z)
    (hB : ∀ x y z w, R x y z w + R y z x w + R z x y w = 0)
    (A : E → E) (a b c d : E → E → ℝ)
    (hA : ∀ x y z w, action R A x y z w =
      2 * (a x y * b z w - c x y * d z w)) (x y z w : E) :
    wedge a b x y z w = wedge c d x y z w := by
  have he := alternation_zero R hfirst hlast hB A x y z w
  simp only [hA] at he
  dsimp only [wedge]
  linear_combination (1 / 2 : ℝ) * he

end QuaternionicSymmetry.CurvatureBianchiWedge
