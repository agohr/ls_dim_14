import QuaternionicSymmetry.ExteriorContinuousWedge
import QuaternionicSymmetry.ContinuousWedgeUnit

/-! Powers in the exterior algebra correspond to normalized repeated wedge
products of continuous alternating forms, including the degree-zero unit. -/
namespace QuaternionicSymmetry.ExteriorContinuousPowers

open Module ExteriorContinuousPairing ExteriorContinuousWedge
  ContinuousWedge ContinuousWedgeUnit
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {d : ℕ}

def castPower {m n : ℕ} (h : m = n) (α : Power V m) : Power V n := by
  cases h
  exact α

def powPower (α : Power V d) (n : ℕ) : Power V (d*n) :=
  ⟨α.val ^ n, by simpa [Nat.mul_comm] using SetLike.pow_mem_graded n α.property⟩

def wedgePower (α : V [⋀^Fin d]→L[ℝ] ℝ) : (n : ℕ) → V [⋀^Fin (d*n)]→L[ℝ] ℝ
  | 0 => oneZero
  | n+1 => castAlt (Nat.mul_succ d n).symm
      (wedge (ContinuousLinearMap.mul ℝ ℝ) (wedgePower α n) α)

@[simp] theorem toContinuous_castPower {m n : ℕ} (h : m = n) (α : Power V m) :
    toContinuous n (castPower h α) = castAlt h (toContinuous m α) := by
  cases h
  rfl

omit [FiniteDimensional ℝ V] in
theorem powPower_succ (α : Power V d) (n : ℕ) :
    powPower α (n+1) =
      castPower (Nat.mul_succ d n).symm (mulPower (powPower α n) α) := by
  have hc {m n : ℕ} (h : m = n) (β : Power V m) : (castPower h β).val = β.val := by
    cases h
    rfl
  apply Subtype.ext
  rw [hc]
  exact pow_succ _ _

theorem toContinuous_powPower (α : Power V d) (n : ℕ) :
    toContinuous (d*n) (powPower α n) = wedgePower (toContinuous d α) n := by
  induction n with
  | zero =>
    have he : powPower α 0 = exteriorPower.ιMulti ℝ 0 (fun i => Fin.elim0 i) := by
      apply Subtype.ext
      simp [powPower]
    rw [he]
    ext v
    simp [toContinuous_apply, wedgePower, oneZero]
  | succ n ih =>
    rw [powPower_succ, toContinuous_castPower, toContinuous_mulPower, ih]
    rfl

omit [FiniteDimensional ℝ V] in
theorem wedge_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {p q : ℕ} (L : W →L[ℝ] V)
    (α : V [⋀^Fin p]→L[ℝ] ℝ) (β : V [⋀^Fin q]→L[ℝ] ℝ) :
    (wedge (ContinuousLinearMap.mul ℝ ℝ) α β).compContinuousLinearMap L =
      wedge (ContinuousLinearMap.mul ℝ ℝ)
        (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) := by
  ext v
  simp only [wedge_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1

omit [FiniteDimensional ℝ V] in
theorem castAlt_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {m n : ℕ} (h : m = n) (L : W →L[ℝ] V) (α : V [⋀^Fin m]→L[ℝ] ℝ) :
    (castAlt h α).compContinuousLinearMap L = castAlt h (α.compContinuousLinearMap L) := by
  cases h
  rfl

omit [FiniteDimensional ℝ V] in
theorem wedgePower_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : W →L[ℝ] V) (α : V [⋀^Fin d]→L[ℝ] ℝ) (n : ℕ) :
    (wedgePower α n).compContinuousLinearMap L =
      wedgePower (α.compContinuousLinearMap L) n := by
  induction n with
  | zero => ext v; simp [wedgePower, oneZero]
  | succ n ih => simp only [wedgePower, castAlt_comp, wedge_comp, ih]

end
end QuaternionicSymmetry.ExteriorContinuousPowers
