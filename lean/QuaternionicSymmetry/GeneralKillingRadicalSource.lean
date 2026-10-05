import Mathlib.Algebra.Lie.Killing
import Mathlib.Analysis.Complex.Basic

/-!
# Knapp's Killing-radical inclusion (BG-L10)

Knapp, *Lie Groups Beyond an Introduction*, second edition, Corollary 1.47,
printed p. 51, states that the radical of the Killing form is contained in
the solvable radical. The scope at the start of section I.7, printed p. 49,
is finite-dimensional Lie algebras over subfields of the complex numbers.
We retain only the complex case. The author's digital second edition is
https://www.math.stonybrook.edu/~aknapp/download/Beyond2-clickable.pdf
(PDF indices 66 and 68).

This is a general published-monograph premise, not a root multiplicity,
Cartan, or twistor classification assumption. The internal application below
still requires a proof that the actual centre is zero.
-/

namespace QuaternionicSymmetry.GeneralKillingRadicalSource

/-- The radical of the literal Killing form is contained in the solvable
radical. `killingCompl` of the whole algebra is precisely that form radical. -/
def KnappKillingRadicalSource : Prop :=
  ∀ (L : Type) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    LieIdeal.killingCompl ℂ L ⊤ ≤ LieAlgebra.radical ℂ L

/-- The centre-free application of BG-L10. Neither reductivity nor a zero
centre is inferred from the literature input alone. -/
theorem isKilling_of_centralRadical_center_eq_bot
    (hKnapp : KnappKillingRadicalSource)
    (L : Type) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.HasCentralRadical ℂ L]
    (hCenter : LieAlgebra.center ℂ L = ⊥) : LieAlgebra.IsKilling ℂ L := by
  constructor
  apply eq_bot_iff.mpr
  simpa only [LieAlgebra.radical_eq_center, hCenter] using hKnapp L

end QuaternionicSymmetry.GeneralKillingRadicalSource
