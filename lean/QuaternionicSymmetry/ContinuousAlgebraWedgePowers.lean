import QuaternionicSymmetry.LocalChernWeilTracePowers

/-! Multiplicative coefficient maps preserve every normalized wedge power
of a continuous two-form, with the project's Chern--Weil degree convention. -/
namespace QuaternionicSymmetry.ContinuousAlgebraWedgePowers
open ContinuousWedge LocalChernWeilTracePowers
noncomputable section
variable {E R A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R] [NormedRing A] [NormedAlgebra ℝ A]

theorem map_wedge {p q : ℕ} (f : R →L[ℝ] A)
    (hmul : ∀ a b : R, f (a * b) = f a * f b)
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    f.compContinuousAlternatingMap (wedge (ContinuousLinearMap.mul ℝ R) α β) =
      wedge (ContinuousLinearMap.mul ℝ A)
        (f.compContinuousAlternatingMap α) (f.compContinuousAlternatingMap β) := by
  apply ContinuousAlternatingMap.ext
  intro v
  change f (wedge (ContinuousLinearMap.mul ℝ R) α β v) = _
  simp only [wedge_apply, map_smul, map_sum, ContinuousLinearMap.mul_apply']
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]
    simp [hmul]
  · rw [h]
    simp [hmul]

def power (α : E [⋀^Fin 2]→L[ℝ] R) :
    (k : ℕ) → E [⋀^Fin (powerDegree k)]→L[ℝ] R
  | 0 => α
  | k + 1 => wedge (ContinuousLinearMap.mul ℝ R) α (power α k)

theorem map_power (f : R →L[ℝ] A)
    (hmul : ∀ a b : R, f (a * b) = f a * f b)
    (α : E [⋀^Fin 2]→L[ℝ] R) (k : ℕ) :
    f.compContinuousAlternatingMap (power α k) =
      power (f.compContinuousAlternatingMap α) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change f.compContinuousAlternatingMap
        (wedge (ContinuousLinearMap.mul ℝ R) α (power α k)) = _
      rw [map_wedge f hmul, ih]
      rfl

theorem power_curvatureForm (Γ : LocalConnection.Form (E := E) (A := R))
    (y : E) (k : ℕ) :
    power (LocalConnectionForms.curvatureForm Γ y) k = curvaturePowerForm Γ k y := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change wedge (ContinuousLinearMap.mul ℝ R) _ (power _ k) = _
      rw [ih]
      rfl


theorem wedge_comp {p q : ℕ} (L : E →L[ℝ] E)
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    (wedge (ContinuousLinearMap.mul ℝ R) α β).compContinuousLinearMap L =
      wedge (ContinuousLinearMap.mul ℝ R)
        (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) := by
  ext v
  simp only [wedge_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1

theorem power_comp (L : E →L[ℝ] E) (α : E [⋀^Fin 2]→L[ℝ] R) (k : ℕ) :
    (power α k).compContinuousLinearMap L = power (α.compContinuousLinearMap L) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (wedge (ContinuousLinearMap.mul ℝ R) α (power α k)).compContinuousLinearMap L = _
      rw [wedge_comp, ih]
      rfl

end
end QuaternionicSymmetry.ContinuousAlgebraWedgePowers
