import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.PowerSeries.Exp

/-! The Taylor series at zero is a ring homomorphism on smooth real functions.
This connects finite formal determinant coefficients to actual derivatives,
without a convergence assumption or a division by spectral discriminants. -/

namespace QuaternionicSymmetry.SmoothTaylorSeries

noncomputable section

def smoothFunctions : Subalgebra ℝ (ℝ → ℝ) where
  carrier := {f : ℝ → ℝ | ContDiff ℝ ⊤ f}
  zero_mem' := by change ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ)); exact contDiff_const
  one_mem' := by change ContDiff ℝ ⊤ (fun _ : ℝ => (1 : ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ⊤ f at hf
    change ContDiff ℝ ⊤ g at hg
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ ⊤ f at hf
    change ContDiff ℝ ⊤ g at hg
    exact hf.mul hg
  algebraMap_mem' := by intro r; change ContDiff ℝ ⊤ (fun _ : ℝ => r); exact contDiff_const

abbrev Smooth := smoothFunctions

theorem smooth (f : Smooth) : ContDiff ℝ ⊤ (f : ℝ → ℝ) := f.property

def series (f : Smooth) : PowerSeries ℝ :=
  PowerSeries.mk fun n => iteratedDeriv n (f : ℝ → ℝ) 0 / (n.factorial : ℝ)

@[simp] theorem coeff_series (f : Smooth) (n : ℕ) :
    PowerSeries.coeff n (series f) = iteratedDeriv n (f : ℝ → ℝ) 0 / (n.factorial : ℝ) :=
  PowerSeries.coeff_mk _ _

private theorem binomial_factorial (n i : ℕ) (hi : i ≤ n) :
    (n.choose i : ℝ) / (n.factorial : ℝ) =
      1 / ((i.factorial : ℝ) * ((n-i).factorial : ℝ)) := by
  have h : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n-i).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hi' : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hni : ((n-i).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  nlinarith [h]

theorem series_mul (f g : Smooth) : series (f * g) = series f * series g := by
  ext n
  rw [coeff_series, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change iteratedDeriv n ((f : ℝ → ℝ) * (g : ℝ → ℝ)) 0 / _ = _
  rw [iteratedDeriv_mul ((smooth f).of_le (by simp)).contDiffAt
    ((smooth g).of_le (by simp)).contDiffAt]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coeff_series]
  have h := binomial_factorial n i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  calc
    _ = ((n.choose i : ℝ) / (n.factorial : ℝ)) *
        iteratedDeriv i (f : ℝ → ℝ) 0 * iteratedDeriv (n-i) (g : ℝ → ℝ) 0 := by ring
    _ = _ := by rw [h]; ring

theorem series_add (f g : Smooth) : series (f + g) = series f + series g := by
  ext n
  rw [map_add, coeff_series, coeff_series, coeff_series]
  change iteratedDeriv n ((f : ℝ → ℝ) + (g : ℝ → ℝ)) 0 / _ = _
  rw [iteratedDeriv_add ((smooth f).of_le (by simp)).contDiffAt
    ((smooth g).of_le (by simp)).contDiffAt, add_div]

/-- The Taylor homomorphism preserves determinants and every finite polynomial
identity, by the ordinary ring-homomorphism laws. -/
def taylorHom : Smooth →+* PowerSeries ℝ where
  toFun := series
  map_zero' := by ext n; simp [series]
  map_one' := by
    ext n
    simp only [coeff_series, PowerSeries.coeff_one]
    change iteratedDeriv n (fun _ : ℝ => (1 : ℝ)) 0 / _ = _
    rw [iteratedDeriv_const]
    split_ifs with hn <;> simp [hn]
  map_add' := series_add
  map_mul' := series_mul

def exponential (r : ℝ) : Smooth :=
  ⟨fun t => Real.exp (r * t), by
    change ContDiff ℝ ⊤ (fun t : ℝ => Real.exp (r * t))
    exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)⟩

def constant (r : ℝ) : Smooth := ⟨fun _ => r, show ContDiff ℝ ⊤ (fun _ : ℝ => r) from contDiff_const⟩

def parameter : Smooth := ⟨id, show ContDiff ℝ ⊤ (id : ℝ → ℝ) from contDiff_id⟩

@[simp] theorem taylor_constant (r : ℝ) : taylorHom (constant r) = PowerSeries.C r := by
  ext n
  rw [show taylorHom (constant r) = series (constant r) from rfl, coeff_series]
  change iteratedDeriv n (fun _ : ℝ => r) 0 / _ = _
  simp [iteratedDeriv_const, PowerSeries.coeff_C]
  split_ifs with hn <;> simp [hn]

@[simp] theorem taylor_parameter : taylorHom parameter = PowerSeries.X := by
  ext n
  rw [show taylorHom parameter = series parameter from rfl, coeff_series]
  change iteratedDeriv n (fun t : ℝ => t) 0 / _ = _
  rw [iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  split_ifs with hn <;> simp [hn]

theorem taylor_exponential (r : ℝ) :
    taylorHom (exponential r) = PowerSeries.rescale r (PowerSeries.exp ℝ) := by
  ext n
  rw [show taylorHom (exponential r) = series (exponential r) from rfl, coeff_series]
  change iteratedDeriv n (fun t => Real.exp (r * t)) 0 / _ = _
  rw [iteratedDeriv_exp_const_mul]
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv]

end
end QuaternionicSymmetry.SmoothTaylorSeries
