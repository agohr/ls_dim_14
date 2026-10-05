import QuaternionicSymmetry.QuaternionicEigenbasisCoordinates
import Mathlib.Tactic.LinearCombination

/-! A kernel-checked eight-dimensional wedge calculation. The three curvature
coefficient two-forms satisfying the quaternionic Bianchi wedge identities
are a common scalar multiple of the three standard quaternionic forms.
The certificates are rational linear combinations of the stated identities. -/
namespace QuaternionicSymmetry.QuaternionicBianchiWedgeEight
noncomputable section

def omega (t : Fin 3) (i j : Fin 8) : ℝ :=
  if i.val / 4 = j.val / 4 then
    ![QuaternionicStructure.omegaICoeff,
      QuaternionicStructure.omegaJCoeff,
      QuaternionicStructure.omegaKCoeff] t
      ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
      ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩
  else 0

def wedge {E : Type*} (a b : E → E → ℝ) (i j k l : E) : ℝ :=
  a i j * b k l - a i k * b j l + a i l * b j k +
    a k l * b i j - a j l * b i k + a j k * b i l

private theorem coefficient_0_0_2
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 0 2 = a 0 0 1 * omega 0 0 2 := by
  have h86 := h 0 2 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h86 ⊢
  all_goals linear_combination h86

private theorem coefficient_0_0_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 0 3 = a 0 0 1 * omega 0 0 3 := by
  have h26 := h 0 1 0 3 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h26 ⊢
  all_goals linear_combination h26

private theorem coefficient_0_0_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 0 4 = a 0 0 1 * omega 0 0 4 := by
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h30 h102 h136 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h18 + -h30 + (-1 / 2 : ℝ) * h102 + (-1 / 2 : ℝ) * h136

private theorem coefficient_0_0_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 0 5 = a 0 0 1 * omega 0 0 5 := by
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h29 h101 h135 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h17 + -h29 + (-1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h135

private theorem coefficient_0_0_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 0 6 = a 0 0 1 * omega 0 0 6 := by
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h32 h100 h134 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h16 + h32 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_0_0_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 0 7 = a 0 0 1 * omega 0 0 7 := by
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h31 h99 h133 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h15 + h31 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_0_1_2
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 1 2 = a 0 0 1 * omega 0 1 2 := by
  have h38 := h 0 1 1 2 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h38 ⊢
  all_goals linear_combination h38

private theorem coefficient_0_1_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 1 3 = a 0 0 1 * omega 0 1 3 := by
  have h110 := h 0 2 1 3 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h110 ⊢
  all_goals linear_combination h110

private theorem coefficient_0_1_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 1 4 = a 0 0 1 * omega 0 1 4 := by
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h36 := h 0 1 1 2 3 7
  have h48 := h 0 1 1 4 5 7
  have h84 := h 0 2 0 2 3 7
  have h96 := h 0 2 0 4 5 7
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h29 h36 h48 h84 h96 h101 h135 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h17 + h29 + h36 + -h48 + h84 + -h96 + (1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h135

private theorem coefficient_0_1_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 1 5 = a 0 0 1 * omega 0 1 5 := by
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h35 := h 0 1 1 2 3 6
  have h47 := h 0 1 1 4 5 6
  have h83 := h 0 2 0 2 3 6
  have h95 := h 0 2 0 4 5 6
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h30 h35 h47 h83 h95 h102 h136 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h18 + -h30 + h35 + -h47 + h83 + -h95 + (-1 / 2 : ℝ) * h102 + (-1 / 2 : ℝ) * h136

private theorem coefficient_0_1_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 1 6 = a 0 0 1 * omega 0 1 6 := by
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h34 := h 0 1 1 2 3 5
  have h50 := h 0 1 1 5 6 7
  have h82 := h 0 2 0 2 3 5
  have h98 := h 0 2 0 5 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h31 h34 h50 h82 h98 h99 h133 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h15 + -h31 + -h34 + h50 + -h82 + h98 + (-1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h133

private theorem coefficient_0_1_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 1 7 = a 0 0 1 * omega 0 1 7 := by
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h33 := h 0 1 1 2 3 4
  have h49 := h 0 1 1 4 6 7
  have h81 := h 0 2 0 2 3 4
  have h97 := h 0 2 0 4 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h32 h33 h49 h81 h97 h100 h134 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h16 + h32 + -h33 + h49 + -h81 + h97 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_0_2_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 2 3 = a 0 0 1 * omega 0 2 3 := by
  have h10 := h 0 1 0 1 4 6
  have h52 := h 0 1 2 3 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h10 h52 ⊢
  all_goals linear_combination -h10 + h52

private theorem coefficient_0_2_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 2 4 = a 0 0 1 * omega 0 2 4 := by
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h81 := h 0 2 0 2 3 4
  have h97 := h 0 2 0 4 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h32 h81 h97 h100 h134 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h16 + h32 + -h81 + h97 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_0_2_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 2 5 = a 0 0 1 * omega 0 2 5 := by
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h82 := h 0 2 0 2 3 5
  have h98 := h 0 2 0 5 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h31 h82 h98 h99 h133 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h15 + -h31 + -h82 + h98 + (-1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h133

private theorem coefficient_0_2_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 2 6 = a 0 0 1 * omega 0 2 6 := by
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h83 := h 0 2 0 2 3 6
  have h95 := h 0 2 0 4 5 6
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h30 h83 h95 h102 h136 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h18 + h30 + -h83 + h95 + (1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_0_2_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 2 7 = a 0 0 1 * omega 0 2 7 := by
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h84 := h 0 2 0 2 3 7
  have h96 := h 0 2 0 4 5 7
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h29 h84 h96 h101 h135 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h17 + -h29 + -h84 + h96 + (-1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h135

private theorem coefficient_0_3_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 3 4 = a 0 0 1 * omega 0 3 4 := by
  have h15 := h 0 1 0 2 3 4
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h99 h133 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h15 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_0_3_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 3 5 = a 0 0 1 * omega 0 3 5 := by
  have h16 := h 0 1 0 2 3 5
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h100 h134 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h16 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_0_3_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 3 6 = a 0 0 1 * omega 0 3 6 := by
  have h17 := h 0 1 0 2 3 6
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h101 h135 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h17 + (1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h135

private theorem coefficient_0_3_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 3 7 = a 0 0 1 * omega 0 3 7 := by
  have h18 := h 0 1 0 2 3 7
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h102 h136 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h18 + (1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_0_4_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 4 5 = a 0 0 1 * omega 0 4 5 := by
  have h19 := h 0 1 0 2 4 5
  have h77 := h 0 2 0 1 4 7
  have h151 := h 1 2 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h19 h77 h151 ⊢
  all_goals linear_combination h19 + -h77 + h151

private theorem coefficient_0_4_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 4 6 = a 0 0 1 * omega 0 4 6 := by
  have h90 := h 0 2 0 3 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h90 ⊢
  all_goals linear_combination h90

private theorem coefficient_0_4_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 4 7 = a 0 0 1 * omega 0 4 7 := by
  have h21 := h 0 1 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h21 ⊢
  all_goals linear_combination h21

private theorem coefficient_0_5_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 5 6 = a 0 0 1 * omega 0 5 6 := by
  have h22 := h 0 1 0 2 5 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h22 ⊢
  all_goals linear_combination h22

private theorem coefficient_0_5_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 5 7 = a 0 0 1 * omega 0 5 7 := by
  have h93 := h 0 2 0 3 5 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h93 ⊢
  all_goals linear_combination h93

private theorem coefficient_0_6_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 0 6 7 = a 0 0 1 * omega 0 6 7 := by
  have h24 := h 0 1 0 2 6 7
  have h77 := h 0 2 0 1 4 7
  have h151 := h 1 2 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h24 h77 h151 ⊢
  all_goals linear_combination h24 + -h77 + h151

private theorem coefficient_1_0_1
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 0 1 = a 0 0 1 * omega 1 0 1 := by
  have h142 := h 1 2 0 1 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h142 ⊢
  all_goals linear_combination h142

private theorem coefficient_1_0_2
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 0 2 = a 0 0 1 * omega 1 0 2 := by
  have h77 := h 0 2 0 1 4 7
  have h151 := h 1 2 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h77 h151 ⊢
  all_goals linear_combination -h77 + h151

private theorem coefficient_1_0_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 0 3 = a 0 0 1 * omega 1 0 3 := by
  have h25 := h 0 1 0 3 4 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h25 ⊢
  all_goals linear_combination -h25

private theorem coefficient_1_0_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 0 4 = a 0 0 1 * omega 1 0 4 := by
  have h15 := h 0 1 0 2 3 4
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h99 h133 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h15 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_1_0_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 0 5 = a 0 0 1 * omega 1 0 5 := by
  have h16 := h 0 1 0 2 3 5
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h100 h134 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h16 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_1_0_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 0 6 = a 0 0 1 * omega 1 0 6 := by
  have h17 := h 0 1 0 2 3 6
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h101 h135 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h17 + (1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h135

private theorem coefficient_1_0_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 0 7 = a 0 0 1 * omega 1 0 7 := by
  have h18 := h 0 1 0 2 3 7
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h102 h136 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h18 + (1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_1_1_2
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 1 2 = a 0 0 1 * omega 1 1 2 := by
  have h37 := h 0 1 1 2 4 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h37 ⊢
  all_goals linear_combination -h37

private theorem coefficient_1_1_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 1 3 = a 0 0 1 * omega 1 1 3 := by
  have h19 := h 0 1 0 2 4 5
  have h41 := h 0 1 1 3 4 5
  have h77 := h 0 2 0 1 4 7
  have h151 := h 1 2 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h19 h41 h77 h151 ⊢
  all_goals linear_combination -h19 + -h41 + h77 + -h151

private theorem coefficient_1_1_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 1 4 = a 0 0 1 * omega 1 1 4 := by
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h33 := h 0 1 1 2 3 4
  have h81 := h 0 2 0 2 3 4
  have h97 := h 0 2 0 4 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h32 h33 h81 h97 h100 h134 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h16 + h32 + -h33 + -h81 + h97 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_1_1_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 1 5 = a 0 0 1 * omega 1 1 5 := by
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h34 := h 0 1 1 2 3 5
  have h82 := h 0 2 0 2 3 5
  have h98 := h 0 2 0 5 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h31 h34 h82 h98 h99 h133 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h15 + -h31 + -h34 + -h82 + h98 + (-1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h133

private theorem coefficient_1_1_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 1 6 = a 0 0 1 * omega 1 1 6 := by
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h35 := h 0 1 1 2 3 6
  have h83 := h 0 2 0 2 3 6
  have h95 := h 0 2 0 4 5 6
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h30 h35 h83 h95 h102 h136 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h18 + h30 + -h35 + -h83 + h95 + (1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_1_1_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 1 7 = a 0 0 1 * omega 1 1 7 := by
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h36 := h 0 1 1 2 3 7
  have h84 := h 0 2 0 2 3 7
  have h96 := h 0 2 0 4 5 7
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h29 h36 h84 h96 h101 h135 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h17 + -h29 + -h36 + -h84 + h96 + (-1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h135

private theorem coefficient_1_2_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 2 3 = a 0 0 1 * omega 1 2 3 := by
  have h186 := h 1 2 2 3 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h186 ⊢
  all_goals linear_combination h186

private theorem coefficient_1_2_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 2 4 = a 0 0 1 * omega 1 2 4 := by
  have h1 := h 0 1 0 1 2 4
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h36 := h 0 1 1 2 3 7
  have h48 := h 0 1 1 4 5 7
  have h84 := h 0 2 0 2 3 7
  have h96 := h 0 2 0 4 5 7
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h1 h17 h29 h36 h48 h84 h96 h101 h135 ⊢
  all_goals linear_combination -h1 + (1 / 2 : ℝ) * h17 + -h29 + -h36 + h48 + -h84 + h96 + (-1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h135

private theorem coefficient_1_2_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 2 5 = a 0 0 1 * omega 1 2 5 := by
  have h2 := h 0 1 0 1 2 5
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h35 := h 0 1 1 2 3 6
  have h47 := h 0 1 1 4 5 6
  have h83 := h 0 2 0 2 3 6
  have h95 := h 0 2 0 4 5 6
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h2 h18 h30 h35 h47 h83 h95 h102 h136 ⊢
  all_goals linear_combination -h2 + (-1 / 2 : ℝ) * h18 + h30 + -h35 + h47 + -h83 + h95 + (1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_1_2_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 2 6 = a 0 0 1 * omega 1 2 6 := by
  have h3 := h 0 1 0 1 2 6
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h34 := h 0 1 1 2 3 5
  have h50 := h 0 1 1 5 6 7
  have h82 := h 0 2 0 2 3 5
  have h98 := h 0 2 0 5 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h3 h15 h31 h34 h50 h82 h98 h99 h133 ⊢
  all_goals linear_combination -h3 + (-1 / 2 : ℝ) * h15 + h31 + h34 + -h50 + h82 + -h98 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_1_2_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 2 7 = a 0 0 1 * omega 1 2 7 := by
  have h4 := h 0 1 0 1 2 7
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h33 := h 0 1 1 2 3 4
  have h49 := h 0 1 1 4 6 7
  have h81 := h 0 2 0 2 3 4
  have h97 := h 0 2 0 4 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h4 h16 h32 h33 h49 h81 h97 h100 h134 ⊢
  all_goals linear_combination -h4 + (1 / 2 : ℝ) * h16 + -h32 + h33 + -h49 + h81 + -h97 + (-1 / 2 : ℝ) * h100 + (-1 / 2 : ℝ) * h134

private theorem coefficient_1_3_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 3 4 = a 0 0 1 * omega 1 3 4 := by
  have h5 := h 0 1 0 1 3 4
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h5 h18 h30 h102 h136 ⊢
  all_goals linear_combination -h5 + (-1 / 2 : ℝ) * h18 + h30 + (1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_1_3_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 3 5 = a 0 0 1 * omega 1 3 5 := by
  have h6 := h 0 1 0 1 3 5
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h6 h17 h29 h101 h135 ⊢
  all_goals linear_combination -h6 + (-1 / 2 : ℝ) * h17 + h29 + (1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h135

private theorem coefficient_1_3_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 3 6 = a 0 0 1 * omega 1 3 6 := by
  have h7 := h 0 1 0 1 3 6
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h7 h16 h32 h100 h134 ⊢
  all_goals linear_combination -h7 + (1 / 2 : ℝ) * h16 + -h32 + (-1 / 2 : ℝ) * h100 + (-1 / 2 : ℝ) * h134

private theorem coefficient_1_3_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 3 7 = a 0 0 1 * omega 1 3 7 := by
  have h8 := h 0 1 0 1 3 7
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h8 h15 h31 h99 h133 ⊢
  all_goals linear_combination -h8 + (1 / 2 : ℝ) * h15 + -h31 + (-1 / 2 : ℝ) * h99 + (-1 / 2 : ℝ) * h133

private theorem coefficient_1_4_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 4 5 = a 0 0 1 * omega 1 4 5 := by
  have h155 := h 1 2 0 3 4 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h155 ⊢
  all_goals linear_combination h155

private theorem coefficient_1_4_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 4 6 = a 0 0 1 * omega 1 4 6 := by
  have h10 := h 0 1 0 1 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h10 ⊢
  all_goals linear_combination -h10

private theorem coefficient_1_4_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 4 7 = a 0 0 1 * omega 1 4 7 := by
  have h11 := h 0 1 0 1 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h11 ⊢
  all_goals linear_combination -h11

private theorem coefficient_1_5_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 5 6 = a 0 0 1 * omega 1 5 6 := by
  have h12 := h 0 1 0 1 5 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h12 ⊢
  all_goals linear_combination -h12

private theorem coefficient_1_5_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 5 7 = a 0 0 1 * omega 1 5 7 := by
  have h13 := h 0 1 0 1 5 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h13 ⊢
  all_goals linear_combination -h13

private theorem coefficient_1_6_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 1 6 7 = a 0 0 1 * omega 1 6 7 := by
  have h160 := h 1 2 0 3 6 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h160 ⊢
  all_goals linear_combination h160

private theorem coefficient_2_0_1
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 0 1 = a 0 0 1 * omega 2 0 1 := by
  have h141 := h 1 2 0 1 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h141 ⊢
  all_goals linear_combination -h141

private theorem coefficient_2_0_2
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 0 2 = a 0 0 1 * omega 2 0 2 := by
  have h85 := h 0 2 0 2 4 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h85 ⊢
  all_goals linear_combination -h85

private theorem coefficient_2_0_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 0 3 = a 0 0 1 * omega 2 0 3 := by
  have h19 := h 0 1 0 2 4 5
  have h77 := h 0 2 0 1 4 7
  have h89 := h 0 2 0 3 4 5
  have h151 := h 1 2 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h19 h77 h89 h151 ⊢
  all_goals linear_combination h19 + -h77 + -h89 + h151

private theorem coefficient_2_0_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 0 4 = a 0 0 1 * omega 2 0 4 := by
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h97 := h 0 2 0 4 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h32 h97 h100 h134 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h16 + -h32 + -h97 + (-1 / 2 : ℝ) * h100 + (-1 / 2 : ℝ) * h134

private theorem coefficient_2_0_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 0 5 = a 0 0 1 * omega 2 0 5 := by
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h98 := h 0 2 0 5 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h31 h98 h99 h133 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h15 + h31 + -h98 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_2_0_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 0 6 = a 0 0 1 * omega 2 0 6 := by
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h95 := h 0 2 0 4 5 6
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h30 h95 h102 h136 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h18 + -h30 + -h95 + (-1 / 2 : ℝ) * h102 + (-1 / 2 : ℝ) * h136

private theorem coefficient_2_0_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 0 7 = a 0 0 1 * omega 2 0 7 := by
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h96 := h 0 2 0 4 5 7
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h29 h96 h101 h135 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h17 + h29 + -h96 + (1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h135

private theorem coefficient_2_1_2
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 1 2 = a 0 0 1 * omega 2 1 2 := by
  have h19 := h 0 1 0 2 4 5
  have h77 := h 0 2 0 1 4 7
  have h103 := h 0 2 1 2 4 5
  have h151 := h 1 2 0 2 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h19 h77 h103 h151 ⊢
  all_goals linear_combination h19 + -h77 + -h103 + h151

private theorem coefficient_2_1_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 1 3 = a 0 0 1 * omega 2 1 3 := by
  have h109 := h 0 2 1 3 4 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h109 ⊢
  all_goals linear_combination -h109

private theorem coefficient_2_1_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 1 4 = a 0 0 1 * omega 2 1 4 := by
  have h15 := h 0 1 0 2 3 4
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h99 h133 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h15 + (-1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_2_1_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 1 5 = a 0 0 1 * omega 2 1 5 := by
  have h16 := h 0 1 0 2 3 5
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h100 h134 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h16 + (-1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_2_1_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 1 6 = a 0 0 1 * omega 2 1 6 := by
  have h17 := h 0 1 0 2 3 6
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h101 h135 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h17 + (-1 / 2 : ℝ) * h101 + (1 / 2 : ℝ) * h135

private theorem coefficient_2_1_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 1 7 = a 0 0 1 * omega 2 1 7 := by
  have h18 := h 0 1 0 2 3 7
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h102 h136 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h18 + (-1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_2_2_3
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 2 3 = a 0 0 1 * omega 2 2 3 := by
  have h185 := h 1 2 2 3 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h185 ⊢
  all_goals linear_combination -h185

private theorem coefficient_2_2_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 2 4 = a 0 0 1 * omega 2 2 4 := by
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h67 := h 0 2 0 1 2 4
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h30 h67 h102 h136 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h18 + -h30 + -h67 + (-1 / 2 : ℝ) * h102 + (-1 / 2 : ℝ) * h136

private theorem coefficient_2_2_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 2 5 = a 0 0 1 * omega 2 2 5 := by
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h68 := h 0 2 0 1 2 5
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h29 h68 h101 h135 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h17 + -h29 + -h68 + (-1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h135

private theorem coefficient_2_2_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 2 6 = a 0 0 1 * omega 2 2 6 := by
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h69 := h 0 2 0 1 2 6
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h32 h69 h100 h134 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h16 + h32 + -h69 + (1 / 2 : ℝ) * h100 + (1 / 2 : ℝ) * h134

private theorem coefficient_2_2_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 2 7 = a 0 0 1 * omega 2 2 7 := by
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h70 := h 0 2 0 1 2 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h31 h70 h99 h133 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h15 + h31 + -h70 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_2_3_4
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 3 4 = a 0 0 1 * omega 2 3 4 := by
  have h17 := h 0 1 0 2 3 6
  have h29 := h 0 1 0 4 5 6
  have h36 := h 0 1 1 2 3 7
  have h48 := h 0 1 1 4 5 7
  have h71 := h 0 2 0 1 3 4
  have h84 := h 0 2 0 2 3 7
  have h96 := h 0 2 0 4 5 7
  have h101 := h 0 2 1 2 3 6
  have h135 := h 1 2 0 1 2 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h17 h29 h36 h48 h71 h84 h96 h101 h135 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h17 + -h29 + -h36 + h48 + -h71 + -h84 + h96 + (-1 / 2 : ℝ) * h101 + (-1 / 2 : ℝ) * h135

private theorem coefficient_2_3_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 3 5 = a 0 0 1 * omega 2 3 5 := by
  have h18 := h 0 1 0 2 3 7
  have h30 := h 0 1 0 4 5 7
  have h35 := h 0 1 1 2 3 6
  have h47 := h 0 1 1 4 5 6
  have h72 := h 0 2 0 1 3 5
  have h83 := h 0 2 0 2 3 6
  have h95 := h 0 2 0 4 5 6
  have h102 := h 0 2 1 2 3 7
  have h136 := h 1 2 0 1 2 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h18 h30 h35 h47 h72 h83 h95 h102 h136 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h18 + h30 + -h35 + h47 + -h72 + -h83 + h95 + (1 / 2 : ℝ) * h102 + (1 / 2 : ℝ) * h136

private theorem coefficient_2_3_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 3 6 = a 0 0 1 * omega 2 3 6 := by
  have h15 := h 0 1 0 2 3 4
  have h31 := h 0 1 0 4 6 7
  have h34 := h 0 1 1 2 3 5
  have h50 := h 0 1 1 5 6 7
  have h73 := h 0 2 0 1 3 6
  have h82 := h 0 2 0 2 3 5
  have h98 := h 0 2 0 5 6 7
  have h99 := h 0 2 1 2 3 4
  have h133 := h 1 2 0 1 2 4
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h15 h31 h34 h50 h73 h82 h98 h99 h133 ⊢
  all_goals linear_combination (-1 / 2 : ℝ) * h15 + h31 + h34 + -h50 + -h73 + h82 + -h98 + (1 / 2 : ℝ) * h99 + (1 / 2 : ℝ) * h133

private theorem coefficient_2_3_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 3 7 = a 0 0 1 * omega 2 3 7 := by
  have h16 := h 0 1 0 2 3 5
  have h32 := h 0 1 0 5 6 7
  have h33 := h 0 1 1 2 3 4
  have h49 := h 0 1 1 4 6 7
  have h74 := h 0 2 0 1 3 7
  have h81 := h 0 2 0 2 3 4
  have h97 := h 0 2 0 4 6 7
  have h100 := h 0 2 1 2 3 5
  have h134 := h 1 2 0 1 2 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h16 h32 h33 h49 h74 h81 h97 h100 h134 ⊢
  all_goals linear_combination (1 / 2 : ℝ) * h16 + -h32 + h33 + -h49 + -h74 + h81 + -h97 + (-1 / 2 : ℝ) * h100 + (-1 / 2 : ℝ) * h134

private theorem coefficient_2_4_5
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 4 5 = a 0 0 1 * omega 2 4 5 := by
  have h149 := h 1 2 0 2 4 5
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h149 ⊢
  all_goals linear_combination -h149

private theorem coefficient_2_4_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 4 6 = a 0 0 1 * omega 2 4 6 := by
  have h76 := h 0 2 0 1 4 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h76 ⊢
  all_goals linear_combination -h76

private theorem coefficient_2_4_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 4 7 = a 0 0 1 * omega 2 4 7 := by
  have h77 := h 0 2 0 1 4 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h77 ⊢
  all_goals linear_combination -h77

private theorem coefficient_2_5_6
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 5 6 = a 0 0 1 * omega 2 5 6 := by
  have h78 := h 0 2 0 1 5 6
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h78 ⊢
  all_goals linear_combination -h78

private theorem coefficient_2_5_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 5 7 = a 0 0 1 * omega 2 5 7 := by
  have h79 := h 0 2 0 1 5 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h79 ⊢
  all_goals linear_combination -h79

private theorem coefficient_2_6_7
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    a 2 6 7 = a 0 0 1 * omega 2 6 7 := by
  have h154 := h 1 2 0 2 6 7
  norm_num [wedge, omega, QuaternionicStructure.omegaICoeff,
    QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at h154 ⊢
  all_goals linear_combination -h154

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem coefficients_upper
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l) :
    ∀ t i j, i < j → a t i j = a 0 0 1 * omega t i j := by
  have h0_0_2 := coefficient_0_0_2 a h
  have h0_0_3 := coefficient_0_0_3 a h
  have h0_0_4 := coefficient_0_0_4 a h
  have h0_0_5 := coefficient_0_0_5 a h
  have h0_0_6 := coefficient_0_0_6 a h
  have h0_0_7 := coefficient_0_0_7 a h
  have h0_1_2 := coefficient_0_1_2 a h
  have h0_1_3 := coefficient_0_1_3 a h
  have h0_1_4 := coefficient_0_1_4 a h
  have h0_1_5 := coefficient_0_1_5 a h
  have h0_1_6 := coefficient_0_1_6 a h
  have h0_1_7 := coefficient_0_1_7 a h
  have h0_2_3 := coefficient_0_2_3 a h
  have h0_2_4 := coefficient_0_2_4 a h
  have h0_2_5 := coefficient_0_2_5 a h
  have h0_2_6 := coefficient_0_2_6 a h
  have h0_2_7 := coefficient_0_2_7 a h
  have h0_3_4 := coefficient_0_3_4 a h
  have h0_3_5 := coefficient_0_3_5 a h
  have h0_3_6 := coefficient_0_3_6 a h
  have h0_3_7 := coefficient_0_3_7 a h
  have h0_4_5 := coefficient_0_4_5 a h
  have h0_4_6 := coefficient_0_4_6 a h
  have h0_4_7 := coefficient_0_4_7 a h
  have h0_5_6 := coefficient_0_5_6 a h
  have h0_5_7 := coefficient_0_5_7 a h
  have h0_6_7 := coefficient_0_6_7 a h
  have h1_0_1 := coefficient_1_0_1 a h
  have h1_0_2 := coefficient_1_0_2 a h
  have h1_0_3 := coefficient_1_0_3 a h
  have h1_0_4 := coefficient_1_0_4 a h
  have h1_0_5 := coefficient_1_0_5 a h
  have h1_0_6 := coefficient_1_0_6 a h
  have h1_0_7 := coefficient_1_0_7 a h
  have h1_1_2 := coefficient_1_1_2 a h
  have h1_1_3 := coefficient_1_1_3 a h
  have h1_1_4 := coefficient_1_1_4 a h
  have h1_1_5 := coefficient_1_1_5 a h
  have h1_1_6 := coefficient_1_1_6 a h
  have h1_1_7 := coefficient_1_1_7 a h
  have h1_2_3 := coefficient_1_2_3 a h
  have h1_2_4 := coefficient_1_2_4 a h
  have h1_2_5 := coefficient_1_2_5 a h
  have h1_2_6 := coefficient_1_2_6 a h
  have h1_2_7 := coefficient_1_2_7 a h
  have h1_3_4 := coefficient_1_3_4 a h
  have h1_3_5 := coefficient_1_3_5 a h
  have h1_3_6 := coefficient_1_3_6 a h
  have h1_3_7 := coefficient_1_3_7 a h
  have h1_4_5 := coefficient_1_4_5 a h
  have h1_4_6 := coefficient_1_4_6 a h
  have h1_4_7 := coefficient_1_4_7 a h
  have h1_5_6 := coefficient_1_5_6 a h
  have h1_5_7 := coefficient_1_5_7 a h
  have h1_6_7 := coefficient_1_6_7 a h
  have h2_0_1 := coefficient_2_0_1 a h
  have h2_0_2 := coefficient_2_0_2 a h
  have h2_0_3 := coefficient_2_0_3 a h
  have h2_0_4 := coefficient_2_0_4 a h
  have h2_0_5 := coefficient_2_0_5 a h
  have h2_0_6 := coefficient_2_0_6 a h
  have h2_0_7 := coefficient_2_0_7 a h
  have h2_1_2 := coefficient_2_1_2 a h
  have h2_1_3 := coefficient_2_1_3 a h
  have h2_1_4 := coefficient_2_1_4 a h
  have h2_1_5 := coefficient_2_1_5 a h
  have h2_1_6 := coefficient_2_1_6 a h
  have h2_1_7 := coefficient_2_1_7 a h
  have h2_2_3 := coefficient_2_2_3 a h
  have h2_2_4 := coefficient_2_2_4 a h
  have h2_2_5 := coefficient_2_2_5 a h
  have h2_2_6 := coefficient_2_2_6 a h
  have h2_2_7 := coefficient_2_2_7 a h
  have h2_3_4 := coefficient_2_3_4 a h
  have h2_3_5 := coefficient_2_3_5 a h
  have h2_3_6 := coefficient_2_3_6 a h
  have h2_3_7 := coefficient_2_3_7 a h
  have h2_4_5 := coefficient_2_4_5 a h
  have h2_4_6 := coefficient_2_4_6 a h
  have h2_4_7 := coefficient_2_4_7 a h
  have h2_5_6 := coefficient_2_5_6 a h
  have h2_5_7 := coefficient_2_5_7 a h
  have h2_6_7 := coefficient_2_6_7 a h
  intro t i j hij
  fin_cases t <;> fin_cases i <;> fin_cases j <;> (try norm_num at hij) <;> first | assumption | norm_num [omega, QuaternionicStructure.omegaICoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem omega_skew (t : Fin 3) (i j : Fin 8) : omega t i j = -omega t j i := by
  fin_cases t <;> fin_cases i <;> fin_cases j <;>
    norm_num [omega, QuaternionicStructure.omegaICoeff,
      QuaternionicStructure.omegaJCoeff, QuaternionicStructure.omegaKCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem coefficients
    (a : Fin 3 → Fin 8 → Fin 8 → ℝ)
    (h : ∀ s t i j k l, wedge (a s) (omega t) i j k l =
      wedge (a t) (omega s) i j k l)
    (hsk : ∀ t i j, a t i j = -a t j i) :
    ∀ t i j, a t i j = a 0 0 1 * omega t i j := by
  intro t i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact coefficients_upper a h t i j hij
  · subst j
    have ha := hsk t i i
    have hw := omega_skew t i i
    have ha0 : a t i i = 0 := by linarith
    have hw0 : omega t i i = 0 := by linarith
    rw [ha0, hw0, mul_zero]
  · rw [hsk, coefficients_upper a h t j i hij, omega_skew t j i]
    ring

end
end QuaternionicSymmetry.QuaternionicBianchiWedgeEight
