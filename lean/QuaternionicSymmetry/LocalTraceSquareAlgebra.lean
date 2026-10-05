import QuaternionicSymmetry.LocalCovariantExterior
import QuaternionicSymmetry.ContinuousAlternation
import QuaternionicSymmetry.ContinuousMultilinearProduct

/-! Algebraic cyclic-trace identities used in the quadratic Chern–Weil
calculation.  These lemmas make the cyclicity hypothesis explicit and do not
assume closure of a characteristic form. -/

namespace QuaternionicSymmetry.LocalTraceSquareAlgebra

noncomputable section

variable {E A B : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem trace_product_symmetric (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a)) (a b : A) :
    T (a * b) = T (b * a) := hT a b

theorem trace_commutator_balance (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a)) (g a b : A) :
    T ((g * a - a * g) * b) + T (a * (g * b - b * g)) = 0 := by
  simp only [sub_mul, mul_sub, map_sub, mul_assoc]
  rw [hT g (a * b)]
  simp only [mul_assoc]
  abel

theorem trace_commutator_left (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a)) (g a b : A) :
    T ((g * a - a * g) * b) = -T (a * (g * b - b * g)) := by
  exact add_eq_zero_iff_eq_neg.mp (trace_commutator_balance T hT g a b)

/-- The three-pairing coordinate expression for one half of the trace of a
curvature two-form wedged with itself. -/
def traceSquare4 (T : A →L[ℝ] B) (F : E → E → A) (a b c d : E) : B :=
  T (F a b * F c d - F a c * F b d + F a d * F b c)

theorem traceSquare4_swap01 (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a))
    (F : E → E → A) (hF : ∀ a b, F b a = -F a b) (a b c d : E) :
    traceSquare4 T F b a c d = -traceSquare4 T F a b c d := by
  simp only [traceSquare4, hF a b, neg_mul, map_add, map_sub, map_neg]
  rw [hT (F b c) (F a d), hT (F b d) (F a c)]
  abel

theorem traceSquare4_swap12 (T : A →L[ℝ] B)
    (F : E → E → A) (hF : ∀ a b, F b a = -F a b) (a b c d : E) :
    traceSquare4 T F a c b d = -traceSquare4 T F a b c d := by
  simp only [traceSquare4, hF b c, mul_neg, map_add, map_sub, map_neg]
  abel

theorem traceSquare4_swap23 (T : A →L[ℝ] B)
    (F : E → E → A) (hF : ∀ a b, F b a = -F a b) (a b c d : E) :
    traceSquare4 T F a b d c = -traceSquare4 T F a b c d := by
  simp only [traceSquare4, hF c d, mul_neg, map_add, map_sub, map_neg]
  abel

theorem traceSquare4_self01 (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a))
    (F : E → E → A) (hF : ∀ a, F a a = 0) (a c d : E) :
    traceSquare4 T F a a c d = 0 := by
  simp only [traceSquare4, hF a, zero_mul, zero_sub, map_add, map_neg]
  rw [hT (F a c) (F a d)]
  abel

theorem traceSquare4_self12 (T : A →L[ℝ] B)
    (F : E → E → A) (hF : ∀ a, F a a = 0) (a b d : E) :
    traceSquare4 T F a b b d = 0 := by
  simp [traceSquare4, hF b]

theorem traceSquare4_self23 (T : A →L[ℝ] B)
    (F : E → E → A) (hF : ∀ a, F a a = 0) (a b c : E) :
    traceSquare4 T F a b c c = 0 := by
  simp [traceSquare4, hF c]

theorem traceSquare4_self02 (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a))
    (F : E → E → A) (hF : ∀ a b, F b a = -F a b)
    (hdiag : ∀ a, F a a = 0) (a b d : E) :
    traceSquare4 T F a b a d = 0 := by
  have hs := traceSquare4_swap01 T hT F hF a b a d
  rw [traceSquare4_self12 T F hdiag b a d] at hs
  exact neg_eq_zero.mp hs.symm

theorem traceSquare4_self13 (T : A →L[ℝ] B)
    (F : E → E → A) (hF : ∀ a b, F b a = -F a b)
    (hdiag : ∀ a, F a a = 0) (a b c : E) :
    traceSquare4 T F a b c b = 0 := by
  have hs := traceSquare4_swap23 T F hF a b b c
  rw [traceSquare4_self12 T F hdiag a b c] at hs
  simpa only [neg_zero] using hs

theorem traceSquare4_self03 (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a))
    (F : E → E → A) (hF : ∀ a b, F b a = -F a b)
    (hdiag : ∀ a, F a a = 0) (a b c : E) :
    traceSquare4 T F a b c a = 0 := by
  have hs := traceSquare4_swap23 T F hF a b a c
  rw [traceSquare4_self02 T hT F hF hdiag a b c] at hs
  simpa only [neg_zero] using hs

theorem traceSquare4_zero_of_eq (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a))
    (F : E → E → A) (hF : ∀ a b, F b a = -F a b)
    (hdiag : ∀ a, F a a = 0) (v : Fin 4 → E)
    (i j : Fin 4) (hij : v i = v j) (hne : i ≠ j) :
    traceSquare4 T F (v 0) (v 1) (v 2) (v 3) = 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact (hne rfl).elim
    | (have h01 : v 0 = v 1 := by first | simpa using hij | simpa using hij.symm
       rw [h01]
       exact traceSquare4_self01 T hT F hdiag _ _ _)
    | (have h02 : v 0 = v 2 := by first | simpa using hij | simpa using hij.symm
       rw [h02]
       exact traceSquare4_self02 T hT F hF hdiag _ _ _)
    | (have h03 : v 0 = v 3 := by first | simpa using hij | simpa using hij.symm
       rw [h03]
       exact traceSquare4_self03 T hT F hF hdiag _ _ _)
    | (have h12 : v 1 = v 2 := by first | simpa using hij | simpa using hij.symm
       rw [h12]
       exact traceSquare4_self12 T F hdiag _ _ _)
    | (have h13 : v 1 = v 3 := by first | simpa using hij | simpa using hij.symm
       rw [h13]
       exact traceSquare4_self13 T F hF hdiag _ _ _)
    | (have h23 : v 2 = v 3 := by first | simpa using hij | simpa using hij.symm
       rw [h23]
       exact traceSquare4_self23 T F hdiag _ _ _)

/-- The ordinary Leibniz variation of the three-pairing trace expression.
The second argument is the variation of the curvature coefficients. -/
def traceSquare4Variation (T : A →L[ℝ] B) (F D : E → E → A)
    (a b c d : E) : B :=
  T (D a b * F c d + F a b * D c d -
    (D a c * F b d + F a c * D b d) +
    (D a d * F b c + F a d * D b c))

theorem traceSquare4Variation_commutator (T : A →L[ℝ] B)
    (hT : ∀ a b : A, T (a * b) = T (b * a))
    (F : E → E → A) (g : A) (a b c d : E) :
    traceSquare4Variation T F (fun u v => g * F u v - F u v * g) a b c d = 0 := by
  simp only [traceSquare4Variation, map_add, map_sub]
  have h₁ := trace_commutator_balance T hT g (F a b) (F c d)
  have h₂ := trace_commutator_balance T hT g (F a c) (F b d)
  have h₃ := trace_commutator_balance T hT g (F a d) (F b c)
  rw [h₁, h₂, h₃]
  abel

theorem traceSquare4Variation_add (T : A →L[ℝ] B)
    (F D₁ D₂ : E → E → A) (a b c d : E) :
    traceSquare4Variation T F (fun v w => D₁ v w + D₂ v w) a b c d =
      traceSquare4Variation T F D₁ a b c d +
      traceSquare4Variation T F D₂ a b c d := by
  simp only [traceSquare4Variation, add_mul, mul_add, map_add, map_sub]
  abel

theorem traceSquare4Variation_covariant_eq_ordinary (T : A →L[ℝ] B)
    (hT : ∀ p q : A, T (p * q) = T (q * p))
    (F D : E → E → A) (g : A) (a b c d : E) :
    traceSquare4Variation T F
      (fun v w => D v w + (g * F v w - F v w * g)) a b c d =
      traceSquare4Variation T F D a b c d := by
  rw [traceSquare4Variation_add]
  rw [traceSquare4Variation_commutator T hT F g a b c d]
  simp

def cyclicDerivative (D : E → E → E → A) (a b c : E) : A :=
  D a b c + D b c a + D c a b

/-- The five-term exterior derivative of the three-pairing expression is the
ten-term shuffle of the cyclic derivative of its two-form input. -/
theorem traceSquare4Variation_five_eq_cyclic (T : A →L[ℝ] B)
    (hT : ∀ p q : A, T (p * q) = T (q * p))
    (F : E → E → A) (D : E → E → E → A)
    (hD : ∀ u v w, D u w v = -D u v w) (a b c d e : E) :
    traceSquare4Variation T F (D a) b c d e -
    traceSquare4Variation T F (D b) a c d e +
    traceSquare4Variation T F (D c) a b d e -
    traceSquare4Variation T F (D d) a b c e +
    traceSquare4Variation T F (D e) a b c d =
      T (cyclicDerivative D a b c * F d e) -
      T (cyclicDerivative D a b d * F c e) +
      T (cyclicDerivative D a b e * F c d) +
      T (cyclicDerivative D a c d * F b e) -
      T (cyclicDerivative D a c e * F b d) +
      T (cyclicDerivative D a d e * F b c) -
      T (cyclicDerivative D b c d * F a e) +
      T (cyclicDerivative D b c e * F a d) -
      T (cyclicDerivative D b d e * F a c) +
      T (cyclicDerivative D c d e * F a b) := by
  simp only [traceSquare4Variation, cyclicDerivative, add_mul, map_add, map_sub]
  rw [hT (F b c) (D a d e), hT (F b d) (D a c e), hT (F b e) (D a c d),
    hT (F a c) (D b d e), hT (F a d) (D b c e), hT (F a e) (D b c d),
    hT (F a b) (D c d e), hT (F a d) (D c b e), hT (F a e) (D c b d),
    hT (F a b) (D d c e), hT (F a c) (D d b e), hT (F a e) (D d b c),
    hT (F a b) (D e c d), hT (F a c) (D e b d), hT (F a d) (D e b c)]
  rw [hD b a c, hD b a d, hD b a e, hD c a d, hD c a e, hD d a e,
    hD c b d, hD c b e, hD d b e, hD d c e]
  simp only [neg_mul, map_neg]
  abel

theorem traceSquare4Variation_five_eq_zero (T : A →L[ℝ] B)
    (hT : ∀ p q : A, T (p * q) = T (q * p))
    (F : E → E → A) (D : E → E → E → A)
    (hD : ∀ u v w, D u w v = -D u v w)
    (hB : ∀ u v w, cyclicDerivative D u v w = 0)
    (a b c d e : E) :
    traceSquare4Variation T F (D a) b c d e -
    traceSquare4Variation T F (D b) a c d e +
    traceSquare4Variation T F (D c) a b d e -
    traceSquare4Variation T F (D d) a b c e +
    traceSquare4Variation T F (D e) a b c d = 0 := by
  rw [traceSquare4Variation_five_eq_cyclic T hT F D hD a b c d e]
  simp only [hB, zero_mul, map_zero, sub_zero, zero_add]

/-- The six-term variation is the actual Fréchet derivative of the
three-pairing trace-square expression. -/
theorem fderiv_traceSquare4
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : A →L[ℝ] B) (φ : E → E → E → A) (x u a b c d : E)
    (hφ : ∀ v w, DifferentiableAt ℝ (fun y => φ y v w) x) :
    fderiv ℝ (fun y => traceSquare4 T (φ y) a b c d) x u =
      traceSquare4Variation T (φ x)
        (fun v w => fderiv ℝ (fun y => φ y v w) x u) a b c d := by
  let gab : E → A := fun y => φ y a b
  let gcd : E → A := fun y => φ y c d
  let gac : E → A := fun y => φ y a c
  let gbd : E → A := fun y => φ y b d
  let gad : E → A := fun y => φ y a d
  let gbc : E → A := fun y => φ y b c
  have h_ab := hφ a b
  have h_cd := hφ c d
  have h_ac := hφ a c
  have h_bd := hφ b d
  have h_ad := hφ a d
  have h_bc := hφ b c
  let g : E → A := fun y => gab y * gcd y - gac y * gbd y + gad y * gbc y
  have hg : DifferentiableAt ℝ g x :=
    ((h_ab.mul h_cd).sub (h_ac.mul h_bd)).add (h_ad.mul h_bc)
  have hd := (T.hasFDerivAt.comp x hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => traceSquare4 T (φ y) a b c d) x =
    T.comp (fderiv ℝ g x) at hd
  have hp₁ := ((h_ab.hasFDerivAt.mul' h_cd.hasFDerivAt).fderiv)
  have hp₂ := ((h_ac.hasFDerivAt.mul' h_bd.hasFDerivAt).fderiv)
  have hp₃ := ((h_ad.hasFDerivAt.mul' h_bc.hasFDerivAt).fderiv)
  have hs := fderiv_sub (h_ab.mul h_cd) (h_ac.mul h_bd)
  have ha := fderiv_add ((h_ab.mul h_cd).sub (h_ac.mul h_bd)) (h_ad.mul h_bc)
  have ha' : fderiv ℝ (fun y => φ y a b * φ y c d - φ y a c * φ y b d +
      φ y a d * φ y b c) x =
      fderiv ℝ (fun y => φ y a b * φ y c d - φ y a c * φ y b d) x +
      fderiv ℝ (fun y => φ y a d * φ y b c) x := ha
  have hs' : fderiv ℝ (fun y => φ y a b * φ y c d - φ y a c * φ y b d) x =
      fderiv ℝ (fun y => φ y a b * φ y c d) x -
      fderiv ℝ (fun y => φ y a c * φ y b d) x := hs
  have hp₁' : fderiv ℝ (fun y => φ y a b * φ y c d) x =
      φ x a b • fderiv ℝ (fun y => φ y c d) x +
      MulOpposite.op (φ x c d) • fderiv ℝ (fun y => φ y a b) x := hp₁
  have hp₂' : fderiv ℝ (fun y => φ y a c * φ y b d) x =
      φ x a c • fderiv ℝ (fun y => φ y b d) x +
      MulOpposite.op (φ x b d) • fderiv ℝ (fun y => φ y a c) x := hp₂
  have hp₃' : fderiv ℝ (fun y => φ y a d * φ y b c) x =
      φ x a d • fderiv ℝ (fun y => φ y b c) x +
      MulOpposite.op (φ x b c) • fderiv ℝ (fun y => φ y a d) x := hp₃
  rw [hd, ContinuousLinearMap.comp_apply]
  dsimp only [g, gab, gcd, gac, gbd, gad, gbc]
  rw [ha', hs', hp₁', hp₂', hp₃']
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, op_smul_eq_mul,
    traceSquare4Variation, map_add, map_sub]
  abel

end
end QuaternionicSymmetry.LocalTraceSquareAlgebra

namespace QuaternionicSymmetry.LocalTraceSquareAlgebra

open ContinuousAlternation

noncomputable section

variable {ι V W : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem alternation_domDomCongr (f : ContinuousMultilinearMap ℝ (fun _ : ι => V) W)
    (τ : Equiv.Perm ι) :
    alternationCLM (f.domDomCongr τ) =
      Equiv.Perm.sign τ • alternationCLM f := by
  ext v
  simp only [alternationCLM_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  let g : Equiv.Perm ι → W := fun ρ =>
    Equiv.Perm.sign (ρ * τ⁻¹) • f (v ∘ ρ)
  calc
    (∑ σ, Equiv.Perm.sign σ • f (fun i => (v ∘ σ) (τ i))) =
        ∑ σ, g (σ * τ) := by
          apply Finset.sum_congr rfl
          intro σ _
          simp [g, Function.comp_def, Equiv.Perm.mul_apply, mul_assoc]
    _ = ∑ ρ, g ρ := Equiv.sum_comp (Equiv.mulRight τ) g
    _ = Equiv.Perm.sign τ • ∑ ρ, Equiv.Perm.sign ρ • f (v ∘ ρ) := by
      simp only [g, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, mul_smul,
        Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      rw [smul_comm]

/-- A three-pairing multilinear map which is already alternating determines
the normalization of the raw four-variable alternation without enumerating
all twenty-four permutations. -/
theorem alternation_three_pairing
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => V) W)
    (τ₁ τ₂ : Equiv.Perm (Fin 4))
    (h₁ : Equiv.Perm.sign τ₁ = -1) (h₂ : Equiv.Perm.sign τ₂ = 1)
    (q : V [⋀^Fin 4]→L[ℝ] W)
    (hq : q.toContinuousMultilinearMap =
      f - f.domDomCongr τ₁ + f.domDomCongr τ₂) :
    alternationCLM f = (8 : ℝ) • q := by
  have H := alternation_of_alternating q
  rw [hq] at H
  simp only [map_add, map_sub, alternation_domDomCongr, h₁, h₂, one_smul] at H
  norm_num at H
  calc
    alternationCLM f = (1 / 3 : ℝ) •
        (alternationCLM f + alternationCLM f + alternationCLM f) := by module
    _ = (1 / 3 : ℝ) • (24 • q) := congrArg _ H
    _ = (8 : ℝ) • q := by module

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

def rawTraceSquare (P : R →L[ℝ] R →L[ℝ] W)
    (F : V [⋀^Fin 2]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => V) W :=
  (ContinuousMultilinearProduct.concatenate P
    F.toContinuousMultilinearMap F.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := 2) (n := 2))

theorem rawTraceSquare_apply (P : R →L[ℝ] R →L[ℝ] W)
    (F : V [⋀^Fin 2]→L[ℝ] R) (v : Fin 4 → V) :
    rawTraceSquare P F v = P (F ![v 0, v 1]) (F ![v 2, v 3]) := by
  simp [rawTraceSquare, ContinuousMultilinearProduct.concatenate_apply,
    ContinuousMultilinearMap.domDomCongr_apply, finSumFinEquiv]
  have hleft : ((fun i : Fin 2 ⊕ Fin 2 =>
      v (Sum.elim (Fin.castAdd 2 : Fin 2 → Fin 4)
        (Fin.natAdd 2 : Fin 2 → Fin 4) i)) ∘ Sum.inl) =
      ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hright : ((fun i : Fin 2 ⊕ Fin 2 =>
      v (Sum.elim (Fin.castAdd 2 : Fin 2 → Fin 4)
        (Fin.natAdd 2 : Fin 2 → Fin 4) i)) ∘ Sum.inr) =
      ![v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright]

private def swap12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

private def cycle132 : Equiv.Perm (Fin 4) :=
  (Equiv.swap 2 3) * (Equiv.swap 1 2)

def traceSquareThreePairing (P : R →L[ℝ] R →L[ℝ] W)
    (F : V [⋀^Fin 2]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => V) W :=
  rawTraceSquare P F - (rawTraceSquare P F).domDomCongr swap12 +
    (rawTraceSquare P F).domDomCongr cycle132

theorem traceSquareThreePairing_apply (T : R →L[ℝ] W)
    (P : R →L[ℝ] R →L[ℝ] W) (hP : ∀ a b, P a b = T (a * b))
    (F : V [⋀^Fin 2]→L[ℝ] R) (v : Fin 4 → V) :
    traceSquareThreePairing P F v =
      traceSquare4 T (fun a b => F ![a, b]) (v 0) (v 1) (v 2) (v 3) := by
  simp [traceSquareThreePairing, swap12, cycle132, rawTraceSquare_apply,
    ContinuousMultilinearMap.domDomCongr_apply, hP, traceSquare4,
    Equiv.swap_apply_def]

theorem twoForm_skew (F : V [⋀^Fin 2]→L[ℝ] R) (a b : V) :
    F ![b, a] = -F ![a, b] := by
  have h := F.toAlternatingMap.map_swap ![a, b] (i := 0) (j := 1) (by decide)
  have he : ![a, b] ∘ Equiv.swap (0 : Fin 2) 1 = ![b, a] := by
    funext i
    fin_cases i <;> simp
  rw [he] at h
  exact h

theorem twoForm_diag (F : V [⋀^Fin 2]→L[ℝ] R) (a : V) :
    F ![a, a] = 0 := by
  exact F.map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) (by simp) (by decide)

def traceSquareThreePairingAlt (T : R →L[ℝ] W)
    (P : R →L[ℝ] R →L[ℝ] W) (hP : ∀ a b, P a b = T (a * b))
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (F : V [⋀^Fin 2]→L[ℝ] R) : V [⋀^Fin 4]→L[ℝ] W :=
  ⟨traceSquareThreePairing P F, by
    intro v i j hij hne
    change traceSquareThreePairing P F v = 0
    rw [traceSquareThreePairing_apply T P hP F v]
    exact traceSquare4_zero_of_eq T hT (fun a b => F ![a, b])
      (twoForm_skew F) (twoForm_diag F) v i j hij hne⟩

theorem traceSquareThreePairingAlt_apply (T : R →L[ℝ] W)
    (P : R →L[ℝ] R →L[ℝ] W) (hP : ∀ a b, P a b = T (a * b))
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (F : V [⋀^Fin 2]→L[ℝ] R) (v : Fin 4 → V) :
    traceSquareThreePairingAlt T P hP hT F v =
      traceSquare4 T (fun a b => F ![a, b]) (v 0) (v 1) (v 2) (v 3) :=
  traceSquareThreePairing_apply T P hP F v

theorem rawTraceSquare_alternation (T : R →L[ℝ] W)
    (P : R →L[ℝ] R →L[ℝ] W) (hP : ∀ a b, P a b = T (a * b))
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (F : V [⋀^Fin 2]→L[ℝ] R) :
    alternationCLM (rawTraceSquare P F) =
      (8 : ℝ) • traceSquareThreePairingAlt T P hP hT F := by
  apply alternation_three_pairing (rawTraceSquare P F) swap12 cycle132
  · decide
  · decide
  · rfl

theorem rawTraceSquare_alternation_apply (T : R →L[ℝ] W)
    (P : R →L[ℝ] R →L[ℝ] W) (hP : ∀ a b, P a b = T (a * b))
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (F : V [⋀^Fin 2]→L[ℝ] R) (a b c d : V) :
    alternationCLM (rawTraceSquare P F) ![a, b, c, d] =
      (8 : ℝ) • traceSquare4 T (fun v w => F ![v, w]) a b c d := by
  rw [rawTraceSquare_alternation T P hP hT F]
  simp [traceSquareThreePairingAlt_apply]

end
end QuaternionicSymmetry.LocalTraceSquareAlgebra
