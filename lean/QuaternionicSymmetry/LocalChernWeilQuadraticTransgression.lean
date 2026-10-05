import QuaternionicSymmetry.LocalChernWeilQuadraticVariation

/-! The local Chern--Simons three-form for the quadratic trace polynomial. -/

namespace QuaternionicSymmetry.LocalChernWeilQuadraticTransgression

open QuaternionicSymmetry.LocalConnection QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalCovariantExterior
  QuaternionicSymmetry.LocalTraceSquareAlgebra
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilQuadraticVariation
  QuaternionicSymmetry.LocalEndomorphismTrace
  QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E [⋀^Fin 1]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 1]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 3]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 3]→L[ℝ] B) := inferInstance

private def raw12 (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) B :=
  (concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap).domDomCongr
    (finSumFinEquiv (m := 1) (n := 2))

private theorem raw12_apply (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) (v : Fin 3 → E) :
    raw12 P α β v = P (α ![v 0]) (β ![v 1, v 2]) := by
  simp [raw12, concatenate_apply, ContinuousMultilinearMap.domDomCongr_apply,
    finSumFinEquiv]
  have hleft : ((fun i : Fin 1 ⊕ Fin 2 =>
      v (Sum.elim (Fin.castAdd 2 : Fin 1 → Fin 3)
        (Fin.natAdd 1 : Fin 2 → Fin 3) i)) ∘ Sum.inl) = ![v 0] := by
    funext i
    fin_cases i; rfl
  have hright : ((fun i : Fin 1 ⊕ Fin 2 =>
      v (Sum.elim (Fin.castAdd 2 : Fin 1 → Fin 3)
        (Fin.natAdd 1 : Fin 2 → Fin 3) i)) ∘ Sum.inr) = ![v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright]

private def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def cycle201 : Equiv.Perm (Fin 3) :=
  (Equiv.swap 1 2) * (Equiv.swap 0 1)

private def threePairing (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) B :=
  raw12 P α β - (raw12 P α β).domDomCongr swap01 +
    (raw12 P α β).domDomCongr cycle201

private theorem threePairing_apply (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) (v : Fin 3 → E) :
    threePairing P α β v =
      P (α ![v 0]) (β ![v 1, v 2]) -
      P (α ![v 1]) (β ![v 0, v 2]) +
      P (α ![v 2]) (β ![v 0, v 1]) := by
  simp [threePairing, swap01, cycle201, raw12_apply,
    ContinuousMultilinearMap.domDomCongr_apply, Equiv.swap_apply_def]

private theorem threePairing_zero01 (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) (a c : E) :
    threePairing P α β ![a, a, c] = 0 := by
  rw [threePairing_apply]
  simp [twoForm_diag]

private theorem threePairing_zero02 (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) (a b : E) :
    threePairing P α β ![a, b, a] = 0 := by
  rw [threePairing_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change P (α ![a]) (β ![b, a]) - P (α ![b]) (β ![a, a]) +
    P (α ![a]) (β ![a, b]) = 0
  rw [twoForm_diag β a, map_zero, twoForm_skew β a b]
  simp

private theorem threePairing_zero12 (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) (a b : E) :
    threePairing P α β ![a, b, b] = 0 := by
  rw [threePairing_apply]
  simp [twoForm_diag]

private def threePairingAlt (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    E [⋀^Fin 3]→L[ℝ] B :=
  ⟨threePairing P α β, by
    intro v i j hij hne
    change threePairing P α β v = 0
    have hv : v = ![v 0, v 1, v 2] := by
      funext k
      fin_cases k <;> rfl
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h : v 0 = v 1 := by simpa using hij
      rw [hv, h]
      exact threePairing_zero01 P α β _ _
    · have h : v 0 = v 2 := by simpa using hij
      rw [hv, h]
      exact threePairing_zero02 P α β _ _
    · have h : v 0 = v 1 := by simpa using hij.symm
      rw [hv, h]
      exact threePairing_zero01 P α β _ _
    · exact (hne rfl).elim
    · have h : v 1 = v 2 := by simpa using hij
      rw [hv, h]
      exact threePairing_zero12 P α β _ _
    · have h : v 0 = v 2 := by simpa using hij.symm
      rw [hv, h]
      exact threePairing_zero02 P α β _ _
    · have h : v 1 = v 2 := by simpa using hij.symm
      rw [hv, h]
      exact threePairing_zero12 P α β _ _
    · exact (hne rfl).elim⟩

/-- The normalized `1∧2` wedge through a coefficient pairing. -/
def wedge12 (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    E [⋀^Fin 3]→L[ℝ] B :=
  (2⁻¹ : ℝ) • alternationCLM (raw12 P α β)

private theorem raw12_alternation (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    alternationCLM (raw12 P α β) = (2 : ℝ) • threePairingAlt P α β := by
  let q := threePairingAlt P α β
  have H := alternation_of_alternating q
  change alternationCLM (threePairing P α β) = 6 • q at H
  have hsign1 : Equiv.Perm.sign swap01 = -1 := by decide
  have hsign2 : Equiv.Perm.sign cycle201 = 1 := by decide
  simp only [threePairing, map_add, map_sub, alternation_domDomCongr,
    hsign1, hsign2, one_smul] at H
  norm_num at H
  calc
    alternationCLM (raw12 P α β) = (1 / 3 : ℝ) •
      (alternationCLM (raw12 P α β) + alternationCLM (raw12 P α β) +
        alternationCLM (raw12 P α β)) := by module
    _ = (1 / 3 : ℝ) • (6 • q) := congrArg _ H
    _ = (2 : ℝ) • q := by module

theorem wedge12_apply (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R)
    (a b c : E) :
    wedge12 P α β ![a, b, c] =
      P (α ![a]) (β ![b, c]) - P (α ![b]) (β ![a, c]) +
      P (α ![c]) (β ![a, b]) := by
  change (2⁻¹ : ℝ) • alternationCLM (raw12 P α β) ![a, b, c] = _
  rw [raw12_alternation]
  simp only [ContinuousAlternatingMap.smul_apply, smul_smul]
  norm_num [threePairingAlt, threePairing_apply]
  simp

private theorem wedge12_add_left (P : R →L[ℝ] R →L[ℝ] B)
    (α₁ α₂ : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    wedge12 P (α₁ + α₂) β = wedge12 P α₁ β + wedge12 P α₂ β := by
  ext v
  simp [wedge12, alternationCLM_apply, raw12_apply, Finset.sum_add_distrib,
    smul_add]

private theorem wedge12_smul_left (P : R →L[ℝ] R →L[ℝ] B)
    (r : ℝ) (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    wedge12 P (r • α) β = r • wedge12 P α β := by
  ext v
  simp [wedge12, alternationCLM_apply, raw12_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  rw [mul_comm (2⁻¹ : ℝ) r]

private theorem wedge12_add_right (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β₁ β₂ : E [⋀^Fin 2]→L[ℝ] R) :
    wedge12 P α (β₁ + β₂) = wedge12 P α β₁ + wedge12 P α β₂ := by
  ext v
  simp [wedge12, alternationCLM_apply, raw12_apply, Finset.sum_add_distrib,
    smul_add]

private theorem wedge12_smul_right (P : R →L[ℝ] R →L[ℝ] B)
    (r : ℝ) (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    wedge12 P α (r • β) = r • wedge12 P α β := by
  ext v
  simp [wedge12, alternationCLM_apply, raw12_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  rw [mul_comm (2⁻¹ : ℝ) r]

private def wedge12Linear (P : R →L[ℝ] R →L[ℝ] B) :
    (E [⋀^Fin 1]→L[ℝ] R) →ₗ[ℝ]
      (E [⋀^Fin 2]→L[ℝ] R) →ₗ[ℝ] E [⋀^Fin 3]→L[ℝ] B :=
  LinearMap.mk₂ ℝ (wedge12 P)
    (wedge12_add_left P) (wedge12_smul_left P)
    (wedge12_add_right P) (wedge12_smul_right P)

private theorem norm_wedge12_le (P : R →L[ℝ] R →L[ℝ] B)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    ‖wedge12 P α β‖ ≤ 3 * ‖P‖ * ‖α‖ * ‖β‖ := by
  let f := concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  let g := f.domDomCongr (finSumFinEquiv (m := 1) (n := 2))
  have h₁ : ‖alternationCLM g‖ ≤ 6 * ‖g‖ := by
    simpa using norm_alternation_le g
  have h₂ : ‖f‖ ≤ ‖P‖ * ‖α‖ * ‖β‖ := by
    simpa only [ContinuousAlternatingMap.norm_toContinuousMultilinearMap] using
      norm_concatenate_le P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  calc
    ‖wedge12 P α β‖ = (2⁻¹ : ℝ) * ‖alternationCLM g‖ := by
      simp [wedge12, raw12, g, f, norm_smul]
    _ ≤ (2⁻¹ : ℝ) * (6 * ‖g‖) := by gcongr
    _ = 3 * ‖f‖ := by
      rw [ContinuousMultilinearMap.norm_domDomCongr]
      ring
    _ ≤ 3 * (‖P‖ * ‖α‖ * ‖β‖) := by gcongr
    _ = 3 * ‖P‖ * ‖α‖ * ‖β‖ := by ring

private def wedge12CLM (P : R →L[ℝ] R →L[ℝ] B) :
    (E [⋀^Fin 1]→L[ℝ] R) →L[ℝ]
      (E [⋀^Fin 2]→L[ℝ] R) →L[ℝ] E [⋀^Fin 3]→L[ℝ] B :=
  (wedge12Linear P).mkContinuous₂ (3 * ‖P‖) (fun α β => norm_wedge12_le P α β)

private theorem differentiableAt_wedge12 (P : R →L[ℝ] R →L[ℝ] B)
    (α : E → E [⋀^Fin 1]→L[ℝ] R)
    (β : E → E [⋀^Fin 2]→L[ℝ] R) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    DifferentiableAt ℝ (fun y => wedge12 P (α y) (β y)) x := by
  have hconst : DifferentiableAt ℝ (fun _ : E =>
      wedge12CLM (E := E) (R := R) (B := B) P) x := differentiableAt_const _
  have hf : DifferentiableAt ℝ (fun y =>
      wedge12CLM (E := E) (R := R) (B := B) P (α y)) x :=
    DifferentiableAt.clm_apply
      (G := E [⋀^Fin 1]→L[ℝ] R)
      (H := (E [⋀^Fin 2]→L[ℝ] R) →L[ℝ] E [⋀^Fin 3]→L[ℝ] B)
      hconst hα
  simpa only [wedge12CLM, wedge12Linear] using hf.clm_apply hβ

/-- The local degree-three Chern--Simons integrand `T(θ∧F_Γ)`. -/
def traceConnectionCurvature (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) : E → E [⋀^Fin 3]→L[ℝ] B :=
  fun x => wedge12 (traceProduct T) (connectionForm θ x) (curvatureForm Γ x)

theorem traceConnectionCurvature_apply (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x a b c : E) :
    traceConnectionCurvature T Γ θ x ![a, b, c] =
      T (θ x a * curvature Γ x b c - θ x b * curvature Γ x a c +
        θ x c * curvature Γ x a b) := by
  simp [traceConnectionCurvature, wedge12_apply, traceProduct_apply,
    connectionForm, oneFormMap_apply, curvatureForm_apply, map_add, map_sub]

theorem differentiableAt_traceConnectionCurvature (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x) :
    DifferentiableAt ℝ (traceConnectionCurvature T Γ θ) x := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x hθ
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hΓ₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact differentiableAt_wedge12 (traceProduct T) (connectionForm θ)
    (curvatureForm Γ) x hθform
    (differentiableAt_curvatureForm Γ x hΓ₁ hΓ₂)

theorem extDeriv_three_apply (ω : E → E [⋀^Fin 3]→L[ℝ] B) (x : E)
    (hω : DifferentiableAt ℝ ω x) (a b c d : E) :
    extDeriv ω x ![a, b, c, d] =
      fderiv ℝ (fun y => ω y ![b, c, d]) x a -
      fderiv ℝ (fun y => ω y ![a, c, d]) x b +
      fderiv ℝ (fun y => ω y ![a, b, d]) x c -
      fderiv ℝ (fun y => ω y ![a, b, c]) x d := by
  have h₁ : Fin.removeNth (1 : Fin 4) ![a, b, c, d] = ![a, c, d] := by
    ext i; fin_cases i <;> rfl
  have h₂ : Fin.removeNth (2 : Fin 4) ![a, b, c, d] = ![a, b, d] := by
    ext i; fin_cases i <;> rfl
  have h₃ : Fin.removeNth (3 : Fin 4) ![a, b, c, d] = ![a, b, c] := by
    ext i; fin_cases i <;> rfl
  rw [extDeriv_apply hω]
  simp [Fin.sum_univ_succ, h₁, h₂, h₃, sub_eq_add_neg]
  abel

private theorem wedge22_trace_self_apply (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (F : E [⋀^Fin 2]→L[ℝ] R) (a b c d : E) :
    wedge22 (traceProduct T) F F ![a, b, c, d] =
      (2 : ℝ) • traceSquare4 T (fun u v => F ![u, v]) a b c d := by
  have h := rawTraceSquare_alternation_apply T (traceProduct T)
    (traceProduct_apply T) hT F a b c d
  change alternationCLM
    ((concatenate (traceProduct T) F.toContinuousMultilinearMap
      F.toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := 2) (n := 2))) ![a, b, c, d] = _ at h
  change (4⁻¹ : ℝ) • alternationCLM
    ((concatenate (traceProduct T) F.toContinuousMultilinearMap
      F.toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := 2) (n := 2))) ![a, b, c, d] = _
  rw [h]
  simp only [smul_smul]
  norm_num

private theorem wedge22_trace_mixed_apply (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (α β : E [⋀^Fin 2]→L[ℝ] R) (a b c d : E) :
    wedge22 (traceProduct T) α β ![a, b, c, d] =
      traceSquare4 T (fun u v => (α + β) ![u, v]) a b c d -
      traceSquare4 T (fun u v => α ![u, v]) a b c d -
      traceSquare4 T (fun u v => β ![u, v]) a b c d := by
  have hsum := wedge22_trace_self_apply T hT (α + β) a b c d
  have hα := wedge22_trace_self_apply T hT α a b c d
  have hβ := wedge22_trace_self_apply T hT β a b c d
  have hsym := wedge22_cyclic (traceProduct T) (fun p q => hT p q) α β
  simp only [wedge22_add_left, wedge22_add_right] at hsum
  simp only [ContinuousAlternatingMap.add_apply] at hsum
  rw [← hsym] at hsum
  rw [hα, hβ] at hsum
  have h₂ : (2 : ℝ) • wedge22 (traceProduct T) α β ![a, b, c, d] =
      (2 : ℝ) • (traceSquare4 T (fun u v => (α + β) ![u, v]) a b c d -
        traceSquare4 T (fun u v => α ![u, v]) a b c d -
        traceSquare4 T (fun u v => β ![u, v]) a b c d) := by
    calc
      (2 : ℝ) • wedge22 (traceProduct T) α β ![a, b, c, d] =
          (2 : ℝ) • traceSquare4 T (fun u v => α ![u, v]) a b c d +
          wedge22 (traceProduct T) α β ![a, b, c, d] +
          (wedge22 (traceProduct T) α β ![a, b, c, d] +
            (2 : ℝ) • traceSquare4 T (fun u v => β ![u, v]) a b c d) -
          (2 : ℝ) • traceSquare4 T (fun u v => α ![u, v]) a b c d -
          (2 : ℝ) • traceSquare4 T (fun u v => β ![u, v]) a b c d := by module
      _ = (2 : ℝ) • traceSquare4 T
          (fun u v => α ![u, v] + β ![u, v]) a b c d -
          (2 : ℝ) • traceSquare4 T (fun u v => α ![u, v]) a b c d -
          (2 : ℝ) • traceSquare4 T (fun u v => β ![u, v]) a b c d := by rw [hsum]
      _ = _ := by
        have hf : (fun u v => (α + β) ![u, v]) =
            (fun u v => α ![u, v] + β ![u, v]) := by
          funext u v
          rfl
        rw [← hf]
        simp only [smul_sub]
  have hh := congrArg (fun z : B => (2⁻¹ : ℝ) • z) h₂
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] using hh

theorem wedge22_trace_apply (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (α β : E [⋀^Fin 2]→L[ℝ] R) (a b c d : E) :
    wedge22 (traceProduct T) α β ![a, b, c, d] =
      T (α ![a, b] * β ![c, d] + β ![a, b] * α ![c, d] -
        (α ![a, c] * β ![b, d] + β ![a, c] * α ![b, d]) +
        (α ![a, d] * β ![b, c] + β ![a, d] * α ![b, c])) := by
  rw [wedge22_trace_mixed_apply T hT]
  simp only [traceSquare4, ContinuousAlternatingMap.add_apply,
    add_mul, mul_add, map_add, map_sub]
  abel

private theorem fderiv_trace_mul (T : R →L[ℝ] B) (f g : E → R)
    (x u : E) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => T (f y * g y)) x u =
      T (fderiv ℝ f x u * g x + f x * fderiv ℝ g x u) := by
  have hp := (hf.hasFDerivAt.mul' hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y * g y) x = _ at hp
  have hc := (T.hasFDerivAt.comp x (hf.mul hg).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => T (f y * g y)) x =
    T.comp (fderiv ℝ (fun y => f y * g y) x) at hc
  rw [hc, ContinuousLinearMap.comp_apply, hp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  simp only [map_add]
  abel

theorem fderiv_traceConnectionCurvature_apply (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x u a b c : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x) :
    fderiv ℝ (fun y => traceConnectionCurvature T Γ θ y ![a, b, c]) x u =
      T (fderiv ℝ (fun y => θ y a) x u * curvature Γ x b c +
          θ x a * fderiv ℝ (fun y => curvature Γ y b c) x u -
        (fderiv ℝ (fun y => θ y b) x u * curvature Γ x a c +
          θ x b * fderiv ℝ (fun y => curvature Γ y a c) x u) +
        (fderiv ℝ (fun y => θ y c) x u * curvature Γ x a b +
          θ x c * fderiv ℝ (fun y => curvature Γ y a b) x u)) := by
  have hθa : DifferentiableAt ℝ (fun y => θ y a) x :=
    hθ.clm_apply (differentiableAt_const _)
  have hθb : DifferentiableAt ℝ (fun y => θ y b) x :=
    hθ.clm_apply (differentiableAt_const _)
  have hθc : DifferentiableAt ℝ (fun y => θ y c) x :=
    hθ.clm_apply (differentiableAt_const _)
  have hFab := differentiableAt_curvature_coefficient Γ x hΓ a b
  have hFac := differentiableAt_curvature_coefficient Γ x hΓ a c
  have hFbc := differentiableAt_curvature_coefficient Γ x hΓ b c
  have hp₁ := fderiv_trace_mul T (fun y => θ y a)
    (fun y => curvature Γ y b c) x u hθa hFbc
  have hp₂ := fderiv_trace_mul T (fun y => θ y b)
    (fun y => curvature Γ y a c) x u hθb hFac
  have hp₃ := fderiv_trace_mul T (fun y => θ y c)
    (fun y => curvature Γ y a b) x u hθc hFab
  have heq : (fun y => traceConnectionCurvature T Γ θ y ![a, b, c]) =
      (fun y => T (θ y a * curvature Γ y b c) -
        T (θ y b * curvature Γ y a c) +
        T (θ y c * curvature Γ y a b)) := by
    funext y
    rw [traceConnectionCurvature_apply]
    simp only [map_add, map_sub]
  have h₁ : DifferentiableAt ℝ (fun y => T (θ y a * curvature Γ y b c)) x :=
    T.differentiableAt.comp x (hθa.mul hFbc)
  have h₂ : DifferentiableAt ℝ (fun y => T (θ y b * curvature Γ y a c)) x :=
    T.differentiableAt.comp x (hθb.mul hFac)
  have h₃ : DifferentiableAt ℝ (fun y => T (θ y c * curvature Γ y a b)) x :=
    T.differentiableAt.comp x (hθc.mul hFab)
  have hsum := fderiv_add (h₁.sub h₂) h₃
  have hsub := fderiv_sub h₁ h₂
  change fderiv ℝ (fun y => T (θ y a * curvature Γ y b c) -
    T (θ y b * curvature Γ y a c) + T (θ y c * curvature Γ y a b)) x = _ at hsum
  change fderiv ℝ (fun y => T (θ y a * curvature Γ y b c) -
    T (θ y b * curvature Γ y a c)) x = _ at hsub
  rw [heq]
  rw [hsum]
  change (fderiv ℝ (fun y => T (θ y a * curvature Γ y b c) -
      T (θ y b * curvature Γ y a c)) x +
    fderiv ℝ (fun y => T (θ y c * curvature Γ y a b)) x) u = _
  rw [hsub]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    hp₁, hp₂, hp₃, map_add, map_sub]

private def csDirectional (θ : E → R) (F : E → E → R)
    (K : E → E → R) (L : E → E → E → R)
    (u a b c : E) : R :=
  K u a * F b c + θ a * L u b c -
    (K u b * F a c + θ b * L u a c) +
    (K u c * F a b + θ c * L u a b)

private def csAlternating (θ : E → R) (F : E → E → R)
    (K : E → E → R) (L : E → E → E → R)
    (a b c d : E) : R :=
  csDirectional θ F K L a b c d - csDirectional θ F K L b a c d +
    csDirectional θ F K L c a b d - csDirectional θ F K L d a b c

private def ordinaryThreeDerivative (L : E → E → E → R) (a b c : E) : R :=
  L a b c - L b a c + L c a b

private def mixedSix (D F : E → E → R) (a b c d : E) : R :=
  D a b * F c d - D a c * F b d + D a d * F b c +
  D c d * F a b - D b d * F a c + D b c * F a d

private theorem wedge22_trace_mixedSix (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (α β : E [⋀^Fin 2]→L[ℝ] R) (a b c d : E) :
    wedge22 (traceProduct T) α β ![a, b, c, d] =
      T (mixedSix (fun u v => α ![u, v]) (fun u v => β ![u, v]) a b c d) := by
  rw [wedge22_trace_apply T hT]
  simp only [mixedSix, map_add, map_sub]
  rw [hT (β ![a, b]) (α ![c, d]),
    hT (β ![a, c]) (α ![b, d]),
    hT (β ![a, d]) (α ![b, c])]
  abel

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAlgebra ℝ R] in
private theorem csAlternating_split (θ : E → R) (F : E → E → R)
    (K : E → E → R) (L : E → E → E → R) (a b c d : E) :
    csAlternating θ F K L a b c d =
      mixedSix (fun u v => K u v - K v u) F a b c d -
      θ a * ordinaryThreeDerivative L b c d +
      θ b * ordinaryThreeDerivative L a c d -
      θ c * ordinaryThreeDerivative L a b d +
      θ d * ordinaryThreeDerivative L a b c := by
  simp only [csAlternating, csDirectional, mixedSix, ordinaryThreeDerivative]
  noncomm_ring

private def commTwo (γ θ : E → R) (u v : E) : R :=
  (γ u * θ v - θ v * γ u) - (γ v * θ u - θ u * γ v)

private def commThree (γ : E → R) (F : E → E → R) (u v w : E) : R :=
  (γ u * F v w - F v w * γ u) -
    (γ v * F u w - F u w * γ v) +
    (γ w * F u v - F u v * γ w)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem cyclic_commutator_six (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (γ θ : E → R) (F : E → E → R) (a b c d : E) :
    T (mixedSix (commTwo γ θ) F a b c d) =
      T (θ a * commThree γ F b c d -
        θ b * commThree γ F a c d +
        θ c * commThree γ F a b d -
        θ d * commThree γ F a b c) := by
  have hrotate (g t f : R) : T (g * t * f) = T (t * f * g) := by
    rw [mul_assoc g t f, hT g (t * f)]
  simp only [mixedSix, commTwo, commThree, map_add, map_sub, sub_mul]
  rw [hrotate (γ a) (θ b) (F c d), hrotate (γ b) (θ a) (F c d),
    hrotate (γ a) (θ c) (F b d), hrotate (γ c) (θ a) (F b d),
    hrotate (γ a) (θ d) (F b c), hrotate (γ d) (θ a) (F b c),
    hrotate (γ c) (θ d) (F a b), hrotate (γ d) (θ c) (F a b),
    hrotate (γ b) (θ d) (F a c), hrotate (γ d) (θ b) (F a c),
    hrotate (γ b) (θ c) (F a d), hrotate (γ c) (θ b) (F a d)]
  simp only [mul_add, mul_sub, map_add, map_sub, ← mul_assoc]
  abel

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem cyclic_cs_algebra (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (γ θ : E → R) (F : E → E → R)
    (K : E → E → R) (L : E → E → E → R)
    (hB : ∀ u v w, ordinaryThreeDerivative L u v w + commThree γ F u v w = 0)
    (a b c d : E) :
    T (csAlternating θ F K L a b c d) =
      T (mixedSix (fun u v => K u v - K v u + commTwo γ θ u v) F a b c d) := by
  rw [csAlternating_split]
  have hb (u v w : E) : ordinaryThreeDerivative L u v w =
      -commThree γ F u v w := add_eq_zero_iff_eq_neg.mp (hB u v w)
  rw [hb b c d, hb a c d, hb a b d, hb a b c]
  simp only [mul_neg]
  have hmix : mixedSix (fun u v => K u v - K v u + commTwo γ θ u v) F a b c d =
      mixedSix (fun u v => K u v - K v u) F a b c d +
        mixedSix (commTwo γ θ) F a b c d := by
    simp only [mixedSix, add_mul]
    noncomm_ring
  rw [hmix]
  simp only [map_add, map_sub, map_neg]
  rw [cyclic_commutator_six T hT γ θ F a b c d]
  simp only [map_add, map_sub]
  abel

private theorem ordinaryThreeDerivative_bianchi
    (Γ : Form (E := E) (A := R)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x)
    (u v w : E) :
    ordinaryThreeDerivative
      (fun p q r => fderiv ℝ (fun y => curvature Γ y q r) x p) u v w +
    commThree (fun p => Γ x p) (fun p q => curvature Γ x p q) u v w = 0 := by
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hΓ₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := congrArg (fun ω : E [⋀^Fin 3]→L[ℝ] R => ω ![u, v, w])
    (LocalConnectionExterior.bianchi_form Γ x hΓ)
  change (extDeriv (curvatureForm Γ) x +
    commutatorForm Γ (curvatureForm Γ x) x) ![u, v, w] = 0 at h
  rw [ContinuousAlternatingMap.add_apply,
    LocalConnectionExterior.extDeriv_curvatureForm_apply Γ x hΓ₁ hΓ₂,
    LocalConnectionExterior.commutatorForm_apply] at h
  simpa only [ordinaryThreeDerivative, commThree, curvatureForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h

private theorem covariantDerivativeForm_as_two_derivatives
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hθ : DifferentiableAt ℝ θ x) (u v : E) :
    covariantDerivativeForm Γ θ x ![u, v] =
      fderiv ℝ (fun y => θ y v) x u - fderiv ℝ (fun y => θ y u) x v +
      commTwo (fun p => Γ x p) (fun p => θ x p) u v := by
  rw [covariantDerivativeForm_apply, covariantDerivative_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    LocalConnectionBianchi.fderiv_eval_const hθ, commTwo]
  noncomm_ring

private theorem extDeriv_traceConnectionCurvature_algebra_apply
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x)
    (a b c d : E) :
    extDeriv (traceConnectionCurvature T Γ θ) x ![a, b, c, d] =
      T (csAlternating (fun v => θ x v) (fun v w => curvature Γ x v w)
        (fun u v => fderiv ℝ (fun y => θ y v) x u)
        (fun u v w => fderiv ℝ (fun y => curvature Γ y v w) x u)
        a b c d) := by
  rw [extDeriv_three_apply (traceConnectionCurvature T Γ θ) x
    (differentiableAt_traceConnectionCurvature T Γ θ x hΓ hθ) a b c d]
  rw [fderiv_traceConnectionCurvature_apply T Γ θ x a b c d hΓ hθ,
    fderiv_traceConnectionCurvature_apply T Γ θ x b a c d hΓ hθ,
    fderiv_traceConnectionCurvature_apply T Γ θ x c a b d hΓ hθ,
    fderiv_traceConnectionCurvature_apply T Γ θ x d a b c hΓ hθ]
  simp only [csAlternating, csDirectional, map_add, map_sub]

/-- Quadratic local transgression: the actual exterior derivative of the
normalized three-form `T(θ∧F_Γ)` is `T((d_Γ θ)∧F_Γ)`. -/
theorem extDeriv_traceConnectionCurvature (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : DifferentiableAt ℝ θ x) :
    extDeriv (traceConnectionCurvature T Γ θ) x =
      wedge22 (traceProduct T) (covariantDerivativeForm Γ θ x) (curvatureForm Γ x) := by
  ext v
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rw [extDeriv_traceConnectionCurvature_algebra_apply T Γ θ x hΓ hθ,
    wedge22_trace_mixedSix T hT]
  have hB : ∀ u w z,
      ordinaryThreeDerivative
        (fun p q r => fderiv ℝ (fun y => curvature Γ y q r) x p) u w z +
        commThree (fun p => Γ x p) (fun p q => curvature Γ x p q) u w z = 0 := by
    intro u w z
    exact ordinaryThreeDerivative_bianchi Γ x hΓ u w z
  rw [cyclic_cs_algebra T hT (fun p => Γ x p) (fun p => θ x p)
    (fun p q => curvature Γ x p q)
    (fun u w => fderiv ℝ (fun y => θ y w) x u)
    (fun u w z => fderiv ℝ (fun y => curvature Γ y w z) x u) hB]
  have hD : (fun u w => fderiv ℝ (fun y => θ y w) x u -
      fderiv ℝ (fun y => θ y u) x w +
      commTwo (fun p => Γ x p) (fun p => θ x p) u w) =
      (fun u w => covariantDerivativeForm Γ θ x ![u, w]) := by
    funext u w
    exact (covariantDerivativeForm_as_two_derivatives Γ θ x hθ u w).symm
  rw [hD]
  simp only [curvatureForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The derivative of the quadratic Chern--Weil form along an affine path is
twice the exterior derivative of the local transgression three-form. -/
theorem traceSquareForm_path_deriv_eq_extDeriv (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) (t : ℝ) :
    deriv (fun s : ℝ => traceSquareForm T (Γ + s • θ) x) t =
      (2 : ℝ) • extDeriv (traceConnectionCurvature T (Γ + t • θ) θ) x := by
  have hΓt : ContDiffAt ℝ 2 (Γ + t • θ) x :=
    hΓ.add (hθ.const_smul t)
  rw [traceSquareForm_path_deriv_cyclic T hT Γ θ x
    (hΓ.differentiableAt (by norm_num))
    (hθ.differentiableAt (by norm_num)) t,
    extDeriv_traceConnectionCurvature T hT (Γ + t • θ) θ x hΓt
      (hθ.differentiableAt (by norm_num))]

theorem extDeriv_const_smul (r : ℝ)
    (ω : E → E [⋀^Fin 3]→L[ℝ] B) (x : E)
    (hω : DifferentiableAt ℝ ω x) :
    extDeriv (fun y => r • ω y) x = r • extDeriv ω x := by
  let L : B →L[ℝ] B := r • ContinuousLinearMap.id ℝ B
  have hmap : DifferentialFormCoefficient.mapForm L ω =
      (fun y => r • ω y) := by
    funext y
    ext v
    simp [DifferentialFormCoefficient.mapForm_apply, L]
  have hcomp : L.compContinuousAlternatingMap (extDeriv ω x) =
      r • extDeriv ω x := by
    ext v
    simp [L]
  rw [← hmap]
  exact (DifferentialFormCoefficient.extDeriv_mapForm L ω x hω).trans hcomp

/-- The local path derivative is the exterior derivative of an actual
normalized three-form. -/
theorem traceSquareForm_path_deriv_transgression (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) (t : ℝ) :
    deriv (fun s : ℝ => traceSquareForm T (Γ + s • θ) x) t =
      extDeriv (fun y => (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y) x := by
  rw [traceSquareForm_path_deriv_eq_extDeriv T hT Γ θ x hΓ hθ t,
    extDeriv_const_smul (2 : ℝ) _ x
      (differentiableAt_traceConnectionCurvature T (Γ + t • θ) θ x
        (hΓ.add (hθ.const_smul t)) (hθ.differentiableAt (by norm_num)))]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- Quadratic local transgression for the actual trace of finite-dimensional
real endomorphisms, with no abstract cyclicity hypothesis. -/
theorem traceCurvatureSquare_path_deriv_transgression
    (Γ θ : Form (E := E) (A := V →L[ℝ] V)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) (t : ℝ) :
    deriv (fun s : ℝ => traceCurvatureSquare (Γ + s • θ) x) t =
      extDeriv (fun y => (2 : ℝ) •
        traceConnectionCurvature traceCLM (Γ + t • θ) θ y) x :=
  traceSquareForm_path_deriv_transgression traceCLM traceCLM_cyclic Γ θ x hΓ hθ t

end
end QuaternionicSymmetry.LocalChernWeilQuadraticTransgression
