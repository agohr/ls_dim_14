import QuaternionicSymmetry.ContinuousWedgeLeibnizLeft
import QuaternionicSymmetry.ContinuousWedgeRightInsertion

/-!
# Graded exterior Leibniz rule for normalized continuous wedges

The proof uses Fréchet's product rule and the checked all-degree shuffle
identities.  The only index transport is the order-preserving reassociation
from `Fin ((p+1)+q)` to `Fin (p+q+1)`.
-/

namespace QuaternionicSymmetry.ContinuousWedgeLeibniz

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeShuffle
  QuaternionicSymmetry.ContinuousWedgeLeibnizLeft
  QuaternionicSymmetry.ContinuousWedgeRightInsertion

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  {p q : ℕ}

/-- The graded exterior Leibniz rule in every pair of degrees, evaluated on
one vector tuple.  The coefficient pairing may be noncommutative. -/
theorem extDeriv_wedge_apply (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin p]→L[ℝ] A)
    (β : E → E [⋀^Fin q]→L[ℝ] B) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x)
    (v : Fin (p + q + 1) → E) :
    extDeriv (fun y => wedge P (α y) (β y)) x v =
      wedge P (extDeriv α x) (β x) (v ∘ wedgeLeftIndex p q) +
        (-1 : ℤ) ^ p • wedge P (α x) (extDeriv β x) v := by
  rw [ContinuousWedge.extDeriv_wedge_apply P α β x hα hβ v]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [alternatizeUncurryFin_wedge_left P (fderiv ℝ α x) (β x) v,
    insertion_wedge_right_eq_signed_wedge_ext P (α x) (fderiv ℝ β x) v]
  rfl

end
end QuaternionicSymmetry.ContinuousWedgeLeibniz
