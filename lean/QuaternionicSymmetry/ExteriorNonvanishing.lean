import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Exterior products of independent vectors are nonzero. -/

namespace QuaternionicSymmetry.ExteriorNonvanishing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem iMulti_ne_zero {n : ℕ} (v : Fin n → V) (hv : LinearIndependent K v) :
    ExteriorAlgebra.ιMulti K n v ≠ 0 := by
  classical
  let s : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin n)).toOrderEmbedding
  have hi := exteriorPower.ιMulti_family_linearIndependent_field n hv
  have hn : exteriorPower.ιMulti K n v ≠ 0 := by
    simpa [exteriorPower.ιMulti_family, s, Function.comp_def] using hi.ne_zero s
  intro h
  apply hn
  apply Subtype.ext
  exact h

end QuaternionicSymmetry.ExteriorNonvanishing
