import QuaternionicSymmetry.LocalChernWeilOrderedTransgression
import QuaternionicSymmetry.ContinuousWedgeAssocComparison
import QuaternionicSymmetry.ContinuousWedgeTraceSwapTwo
import QuaternionicSymmetry.LocalCurvaturePowerMultiplication

/-! Cyclic normalization of the ordered Chern--Simons primitive. -/

namespace QuaternionicSymmetry.LocalChernWeilOrderedNormalization

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeAssocComparison
  QuaternionicSymmetry.ContinuousWedgeTraceSwapTwo
  QuaternionicSymmetry.LocalCurvaturePowerMultiplication

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

private def mulPair : R →L[ℝ] R →L[ℝ] R := ContinuousLinearMap.mul ℝ R

private def traceCast {m n : ℕ} (h : m = n)
    (ω : E [⋀^Fin m]→L[ℝ] B) : E [⋀^Fin n]→L[ℝ] B := by
  cases h
  exact ω

@[simp] private theorem traceCast_apply {m n : ℕ} (h : m = n)
    (ω : E [⋀^Fin m]→L[ℝ] B) (v : Fin n → E) :
    traceCast h ω v = ω (v ∘ finCongr h) := by
  cases h
  rfl

private theorem traceCast_trans {a b c : ℕ} (h₁ : a = b) (h₂ : b = c)
    (ω : E [⋀^Fin a]→L[ℝ] B) :
    traceCast (h₁.trans h₂) ω = traceCast h₂ (traceCast h₁ ω) := by
  cases h₁
  cases h₂
  rfl

private theorem traceCast_wedge_right {q r r' : ℕ} (h : r = r')
    (α : E [⋀^Fin q]→L[ℝ] R)
    (β : E [⋀^Fin r]→L[ℝ] R) (T : R →L[ℝ] B) :
    traceCast (congrArg (q + ·) h)
      (wedge (traceProduct T) α β) =
      wedge (traceProduct T) α (degreeCast h β) := by
  cases h
  rfl

private theorem traceCast_add {m n : ℕ} (h : m = n)
    (ω η : E [⋀^Fin m]→L[ℝ] B) :
    traceCast h (ω + η) = traceCast h ω + traceCast h η := by
  cases h
  rfl

private theorem traceCast_smul {m n : ℕ} (h : m = n)
    (c : ℝ) (ω : E [⋀^Fin m]→L[ℝ] B) :
    traceCast h (c • ω) = c • traceCast h ω := by
  cases h
  rfl

private theorem traceCast_comp {m n : ℕ} (h : m = n)
    (T : R →L[ℝ] B) (ω : E [⋀^Fin m]→L[ℝ] R) :
    traceCast h (T.compContinuousAlternatingMap ω) =
      T.compContinuousAlternatingMap (degreeCast h ω) := by
  cases h
  rfl

private theorem traceCast_congr {m n : ℕ} (h h' : m = n)
    (ω : E [⋀^Fin m]→L[ℝ] B) :
    traceCast h ω = traceCast h' ω := by
  have hh : h = h' := Subsingleton.elim _ _
  rw [hh]

private theorem traceCast_wedge_left {p p' q : ℕ} (h : p = p')
    (α : E [⋀^Fin p]→L[ℝ] R)
    (β : E [⋀^Fin q]→L[ℝ] R) (T : R →L[ℝ] B) :
    traceCast (congrArg (· + q) h)
      (wedge (traceProduct T) α β) =
      wedge (traceProduct T) (degreeCast h α) β := by
  cases h
  rfl

private theorem traceCast_wedge_left_through {p p' q n : ℕ}
    (h : p = p') (h' : p' + q = n)
    (α : E [⋀^Fin p]→L[ℝ] R)
    (β : E [⋀^Fin q]→L[ℝ] R) (T : R →L[ℝ] B) :
    traceCast h' (wedge (traceProduct T) (degreeCast h α) β) =
      traceCast ((congrArg (· + q) h).trans h')
        (wedge (traceProduct T) α β) := by
  calc
    traceCast h' (wedge (traceProduct T) (degreeCast h α) β) =
        traceCast h'
          (traceCast (congrArg (· + q) h)
            (wedge (traceProduct T) α β)) := by
      rw [traceCast_wedge_left]
    _ = traceCast ((congrArg (· + q) h).trans h')
          (wedge (traceProduct T) α β) :=
      (traceCast_trans (congrArg (· + q) h) h' _).symm

private def appendIndex : ℕ → ℕ → ℕ
  | 0, l => l
  | k + 1, l => appendIndex k (concatIndex l 0)

private theorem appendIndex_eq (k l : ℕ) : appendIndex k l = k + l := by
  induction k generalizing l with
  | zero => simp [appendIndex]
  | succ k ih =>
      change appendIndex k (concatIndex l 0) = k + 1 + l
      rw [ih, concatIndex_eq]
      omega

private theorem primitiveDegree_eq (k : ℕ) :
    primitiveDegree k = 2 * k + 1 := by
  cases k with
  | zero => rfl
  | succ k =>
      simp only [primitiveDegree, powerDegree_eq]
      omega

private theorem appendDegree (k l : ℕ) :
    primitiveDegree k + powerDegree l =
      1 + powerDegree (appendIndex k l) := by
  rw [primitiveDegree_eq, powerDegree_eq, appendIndex_eq, powerDegree_eq]
  omega

private theorem concatIndex_append (k l : ℕ) :
    concatIndex k l = appendIndex (k + 1) l := by
  rw [concatIndex_eq, appendIndex_eq]
  omega

private theorem trace_rotate_three (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    {q r : ℕ} (α : E [⋀^Fin 2]→L[ℝ] R)
    (β : E [⋀^Fin q]→L[ℝ] R)
    (γ : E [⋀^Fin r]→L[ℝ] R)
    (v : Fin ((2 + q) + r) → E) :
    wedge (traceProduct T) (wedge mulPair α β) γ v =
      wedge (traceProduct T) β (wedge mulPair γ α)
        (v ∘ finCongr (show q + (r + 2) = (2 + q) + r by omega)) := by
  have hAssoc : ∀ a b c : R,
      traceProduct T (mulPair a b) c =
        traceProduct T a (mulPair b c) := by
    intro a b c
    change T ((a * b) * c) = T (a * (b * c))
    rw [mul_assoc]
  let v₁ : Fin (2 + (q + r)) → E :=
    v ∘ (finCongr (Nat.add_assoc 2 q r)).symm
  let v₂ : Fin ((q + r) + 2) → E :=
    v₁ ∘ finCongr (Nat.add_comm (q + r) 2)
  let v₃ : Fin (q + (r + 2)) → E :=
    v₂ ∘ (finCongr (Nat.add_assoc q r 2)).symm
  calc
    wedge (traceProduct T) (wedge mulPair α β) γ v =
        wedge (traceProduct T) α (wedge mulPair β γ) v₁ := by
      exact wedge_assoc_apply (E := E) (A := R) (B := R)
        (C := R) (D := R) (Y := R) (Z := B)
        (p := 2) (q := q) (r := r)
        mulPair (traceProduct T) mulPair (traceProduct T)
        hAssoc α β γ v
    _ = wedge (traceProduct T) (wedge mulPair β γ) α v₂ := by
      exact wedge_traceProduct_swap_two T hT α
        (wedge mulPair β γ) v₁
    _ = wedge (traceProduct T) β (wedge mulPair γ α) v₃ := by
      exact wedge_assoc_apply (E := E) (A := R) (B := R)
        (C := R) (D := R) (Y := R) (Z := B)
        (p := q) (q := r) (r := 2)
        mulPair (traceProduct T) mulPair (traceProduct T)
        hAssoc β γ α v₂
    _ = wedge (traceProduct T) β (wedge mulPair γ α)
        (v ∘ finCongr (show q + (r + 2) = (2 + q) + r by omega)) := by
      have hv : v₃ =
          (v ∘ finCongr (show q + (r + 2) = (2 + q) + r by omega)) := by
        funext i
        change v ((finCongr (Nat.add_assoc 2 q r)).symm
          (finCongr (Nat.add_comm (q + r) 2)
            ((finCongr (Nat.add_assoc q r 2)).symm i))) = _
        congr 1
      rw [hv]

private theorem trace_rotate_three_cast (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    {q r : ℕ} (α : E [⋀^Fin 2]→L[ℝ] R)
    (β : E [⋀^Fin q]→L[ℝ] R)
    (γ : E [⋀^Fin r]→L[ℝ] R) :
    traceCast (show (2 + q) + r = q + (r + 2) by omega)
      (wedge (traceProduct T) (wedge mulPair α β) γ) =
      wedge (traceProduct T) β (wedge mulPair γ α) := by
  ext v
  rw [traceCast_apply]
  have h := trace_rotate_three T hT α β γ
    (v ∘ finCongr (show (2 + q) + r = q + (r + 2) by omega))
  simpa only [Function.comp_def, finCongr_apply_coe] using h

private theorem trace_curvature_rotate_append (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (x : E) (l q : ℕ)
    (β : E [⋀^Fin q]→L[ℝ] R) :
    traceCast (show (2 + q) + powerDegree l =
        q + powerDegree (concatIndex l 0) by
          have hd := powerDegree_concat l 0
          simp only [powerDegree] at hd
          omega)
      (wedge (traceProduct T)
        (wedge mulPair (curvatureForm Γ x) β)
        (curvaturePowerForm Γ l x)) =
      wedge (traceProduct T) β
        (curvaturePowerForm Γ (concatIndex l 0) x) := by
  let h₁ : (2 + q) + powerDegree l = q + (powerDegree l + 2) := by omega
  let h₂ : powerDegree l + 2 = powerDegree (concatIndex l 0) := by
    simpa only [powerDegree] using powerDegree_concat l 0
  have hfinal : (2 + q) + powerDegree l =
      q + powerDegree (concatIndex l 0) :=
    h₁.trans (congrArg (q + ·) h₂)
  have hc : traceCast hfinal
      (wedge (traceProduct T)
        (wedge mulPair (curvatureForm Γ x) β)
        (curvaturePowerForm Γ l x)) =
      wedge (traceProduct T) β
        (curvaturePowerForm Γ (concatIndex l 0) x) := by
    rw [traceCast_trans h₁ (congrArg (q + ·) h₂)
      (wedge (traceProduct T)
        (wedge mulPair (curvatureForm Γ x) β)
        (curvaturePowerForm Γ l x))]
    rw [trace_rotate_three_cast T hT
      (curvatureForm Γ x) β (curvaturePowerForm Γ l x)]
    rw [traceCast_wedge_right h₂ β
      (wedge mulPair (curvaturePowerForm Γ l x)
        (curvatureForm Γ x)) T]
    rw [show curvatureForm Γ x = curvaturePowerForm Γ 0 x from rfl]
    exact congrArg (wedge (traceProduct T) β)
      (curvaturePowerForm_mul Γ l 0 x)
  exact hc

private theorem trace_connection_curvature_append (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E) (i j : ℕ) :
    traceCast
      ((Nat.add_assoc 1 (powerDegree i) (powerDegree j)).trans
        (congrArg (1 + ·) (powerDegree_concat i j)))
      (wedge (traceProduct T)
        (wedge mulPair (connectionForm θ x)
          (curvaturePowerForm Γ i x))
        (curvaturePowerForm Γ j x)) =
      wedge (traceProduct T) (connectionForm θ x)
        (curvaturePowerForm Γ (concatIndex i j) x) := by
  rw [← mapForm_wedge_mul T
    (wedge mulPair (connectionForm θ x) (curvaturePowerForm Γ i x))
    (curvaturePowerForm Γ j x)]
  rw [← mapForm_wedge_mul T (connectionForm θ x)
    (curvaturePowerForm Γ (concatIndex i j) x)]
  rw [traceCast_comp]
  exact congrArg T.compContinuousAlternatingMap
    (connection_curvaturePowerForm_mul Γ θ i j x)

private theorem trace_connection_indexCast (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    {i j : ℕ} (h : i = j) :
    traceCast (congrArg (fun n => 1 + powerDegree n) h)
      (wedge (traceProduct T) (connectionForm θ x)
        (curvaturePowerForm Γ i x)) =
      wedge (traceProduct T) (connectionForm θ x)
        (curvaturePowerForm Γ j x) := by
  cases h
  rfl

private theorem trace_swap_two_cast (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    {q : ℕ} (α : E [⋀^Fin 2]→L[ℝ] R)
    (β : E [⋀^Fin q]→L[ℝ] R) :
    traceCast (Nat.add_comm 2 q)
      (wedge (traceProduct T) α β) =
      wedge (traceProduct T) β α := by
  ext v
  rw [traceCast_apply]
  have h := wedge_traceProduct_swap_two T hT α β
    (v ∘ finCongr (Nat.add_comm 2 q))
  simpa only [Function.comp_def, finCongr_apply_coe] using h

private theorem trace_comp_add (T : R →L[ℝ] B)
    {m : ℕ} (ω η : E [⋀^Fin m]→L[ℝ] R) :
    T.compContinuousAlternatingMap (ω + η) =
      T.compContinuousAlternatingMap ω +
        T.compContinuousAlternatingMap η := by
  ext v
  simp

private theorem trace_ordered_append_power (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E) :
    ∀ k l : ℕ,
      traceCast (appendDegree k l)
        (wedge (traceProduct T)
          (orderedPrimitive Γ θ k x)
          (curvaturePowerForm Γ l x)) =
        ((k + 1 : ℕ) : ℝ) •
          wedge (traceProduct T) (connectionForm θ x)
            (curvaturePowerForm Γ (appendIndex k l) x) := by
  intro k
  induction k with
  | zero =>
      intro l
      simp only [orderedPrimitive, appendIndex, Nat.zero_add,
        Nat.cast_one, one_smul]
      have h : appendDegree 0 l =
          (show primitiveDegree 0 + powerDegree l =
            1 + powerDegree (appendIndex 0 l) by rfl) :=
        Subsingleton.elim _ _
      rw [h]
      rfl
  | succ k ih =>
      intro l
      let F := curvatureForm Γ x
      let Pk := curvaturePowerForm Γ k x
      let Pl := curvaturePowerForm Γ l x
      let S := orderedPrimitive Γ θ k x
      let A := wedge mulPair (connectionForm θ x) Pk
      let D := wedge mulPair F S
      let hA : 1 + powerDegree k = primitiveDegree (k + 1) := rfl
      let hD : 2 + primitiveDegree k = primitiveDegree (k + 1) :=
        primitiveDegree_succ_cast k
      let hOut := appendDegree (k + 1) l
      let C : E [⋀^Fin (1 + powerDegree (appendIndex (k + 1) l))]→L[ℝ] B :=
        wedge (traceProduct T) (connectionForm θ x)
          (curvaturePowerForm Γ (appendIndex (k + 1) l) x)
      have hLeft :
          traceCast hOut
            (wedge (traceProduct T) (degreeCast hA A) Pl) = C := by
        let hFirst : (1 + powerDegree k) + powerDegree l =
            1 + powerDegree (appendIndex (k + 1) l) :=
          (congrArg (· + powerDegree l) hA).trans hOut
        let hConcat :=
          (Nat.add_assoc 1 (powerDegree k) (powerDegree l)).trans
            (congrArg (1 + ·) (powerDegree_concat k l))
        let hIdx : concatIndex k l = appendIndex (k + 1) l :=
          concatIndex_append k l
        let hEnd := congrArg (fun n => 1 + powerDegree n) hIdx
        calc
          traceCast hOut
              (wedge (traceProduct T) (degreeCast hA A) Pl) =
            traceCast hFirst (wedge (traceProduct T) A Pl) :=
              traceCast_wedge_left_through hA hOut A Pl T
          _ = traceCast hEnd
                (traceCast hConcat (wedge (traceProduct T) A Pl)) := by
            exact (traceCast_congr hFirst (hConcat.trans hEnd) _).trans
              (traceCast_trans hConcat hEnd _)
          _ = traceCast hEnd
                (wedge (traceProduct T) (connectionForm θ x)
                  (curvaturePowerForm Γ (concatIndex k l) x)) := by
            exact congrArg (traceCast hEnd)
              (trace_connection_curvature_append T Γ θ x k l)
          _ = C := trace_connection_indexCast T Γ θ x hIdx
      have hRight :
          traceCast hOut
            (wedge (traceProduct T) (degreeCast hD D) Pl) =
              ((k + 1 : ℕ) : ℝ) • C := by
        let l' := concatIndex l 0
        let hSecond : (2 + primitiveDegree k) + powerDegree l =
            1 + powerDegree (appendIndex (k + 1) l) :=
          (congrArg (· + powerDegree l) hD).trans hOut
        let hRotate : (2 + primitiveDegree k) + powerDegree l =
            primitiveDegree k + powerDegree l' := by
          dsimp [l']
          have hd := powerDegree_concat l 0
          simp only [powerDegree] at hd
          omega
        let hIH := appendDegree k l'
        calc
          traceCast hOut
              (wedge (traceProduct T) (degreeCast hD D) Pl) =
            traceCast hSecond (wedge (traceProduct T) D Pl) :=
              traceCast_wedge_left_through hD hOut D Pl T
          _ = traceCast hIH
                (traceCast hRotate (wedge (traceProduct T) D Pl)) := by
            exact (traceCast_congr hSecond (hRotate.trans hIH) _).trans
              (traceCast_trans hRotate hIH _)
          _ = traceCast hIH
                (wedge (traceProduct T) S
                  (curvaturePowerForm Γ l' x)) := by
            exact congrArg (traceCast hIH)
              (trace_curvature_rotate_append T hT Γ x l
                (primitiveDegree k) S)
          _ = ((k + 1 : ℕ) : ℝ) • C := ih l'
      change traceCast hOut
        (wedge (traceProduct T) (degreeCast hA A + degreeCast hD D) Pl) =
          ((k + 1 + 1 : ℕ) : ℝ) • C
      rw [wedge_add_left, traceCast_add, hLeft, hRight]
      calc
        C + ((k + 1 : ℕ) : ℝ) • C =
            (1 : ℝ) • C + ((k + 1 : ℕ) : ℝ) • C := by simp
        _ = ((1 : ℝ) + ((k + 1 : ℕ) : ℝ)) • C := by rw [add_smul]
        _ = ((k + 1 + 1 : ℕ) : ℝ) • C := by
          congr 1
          push_cast
          ring

private theorem trace_curvature_ordered (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E) (k : ℕ) :
    traceCast (primitiveDegree_succ_cast k)
      (wedge (traceProduct T)
        (curvatureForm Γ x) (orderedPrimitive Γ θ k x)) =
      ((k + 1 : ℕ) : ℝ) •
        wedge (traceProduct T) (connectionForm θ x)
          (curvaturePowerForm Γ k x) := by
  let hSwap := Nat.add_comm 2 (primitiveDegree k)
  let hAppend := appendDegree k 0
  let hIdx : appendIndex k 0 = k := by
    simpa using appendIndex_eq k 0
  let hEnd := congrArg (fun n => 1 + powerDegree n) hIdx
  have hTotal : 2 + primitiveDegree k = primitiveDegree (k + 1) :=
    hSwap.trans (hAppend.trans hEnd)
  calc
    traceCast (primitiveDegree_succ_cast k)
        (wedge (traceProduct T)
          (curvatureForm Γ x) (orderedPrimitive Γ θ k x)) =
      traceCast hTotal
        (wedge (traceProduct T)
          (curvatureForm Γ x) (orderedPrimitive Γ θ k x)) :=
        traceCast_congr _ _ _
    _ = traceCast hEnd (traceCast hAppend
          (traceCast hSwap
            (wedge (traceProduct T)
              (curvatureForm Γ x) (orderedPrimitive Γ θ k x)))) := by
        rw [traceCast_trans hSwap (hAppend.trans hEnd),
          traceCast_trans hAppend hEnd]
    _ = traceCast hEnd (traceCast hAppend
          (wedge (traceProduct T)
            (orderedPrimitive Γ θ k x) (curvatureForm Γ x))) := by
        rw [trace_swap_two_cast T hT]
    _ = traceCast hEnd
          (((k + 1 : ℕ) : ℝ) •
            wedge (traceProduct T) (connectionForm θ x)
              (curvaturePowerForm Γ (appendIndex k 0) x)) := by
        exact congrArg (traceCast hEnd)
          (trace_ordered_append_power T hT Γ θ x k 0)
    _ = ((k + 1 : ℕ) : ℝ) •
          wedge (traceProduct T) (connectionForm θ x)
            (curvaturePowerForm Γ k x) := by
        rw [traceCast_smul]
        exact congrArg (((k + 1 : ℕ) : ℝ) • ·)
          (trace_connection_indexCast T Γ θ x hIdx)

/-- The degree-one base primitive is the path-direction form. -/
theorem trace_orderedPrimitive_zero (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E) :
    T.compContinuousAlternatingMap (orderedPrimitive Γ θ 0 x) =
      T.compContinuousAlternatingMap (connectionForm θ x) := rfl

/-- Cyclicity converts the ordered primitive with `k+1` curvature factors
to the textbook's `(k+2) T(θ∧F^(k+1))` form. -/
theorem trace_orderedPrimitive_succ (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E) (k : ℕ) :
    T.compContinuousAlternatingMap (orderedPrimitive Γ θ (k + 1) x) =
      ((k + 2 : ℕ) : ℝ) • traceConnectionCurvaturePower T Γ θ k x := by
  let hA : 1 + powerDegree k = primitiveDegree (k + 1) := rfl
  let hD : 2 + primitiveDegree k = primitiveDegree (k + 1) :=
    primitiveDegree_succ_cast k
  let A := wedge mulPair (connectionForm θ x)
    (curvaturePowerForm Γ k x)
  let D := wedge mulPair (curvatureForm Γ x)
    (orderedPrimitive Γ θ k x)
  let C := traceConnectionCurvaturePower T Γ θ k x
  have hFirst : traceCast hA
      (wedge (traceProduct T) (connectionForm θ x)
        (curvaturePowerForm Γ k x)) = C := by
    have hh : hA = (rfl : 1 + powerDegree k = primitiveDegree (k + 1)) :=
      Subsingleton.elim _ _
    rw [hh]
    rfl
  change T.compContinuousAlternatingMap
    (degreeCast hA A + degreeCast hD D) = ((k + 2 : ℕ) : ℝ) • C
  rw [trace_comp_add]
  rw [← traceCast_comp hA T A, ← traceCast_comp hD T D]
  dsimp only [A, D, mulPair]
  rw [mapForm_wedge_mul, mapForm_wedge_mul]
  rw [hFirst, trace_curvature_ordered T hT Γ θ x k]
  calc
    C + ((k + 1 : ℕ) : ℝ) • C =
        (1 : ℝ) • C + ((k + 1 : ℕ) : ℝ) • C := by simp
    _ = ((1 : ℝ) + ((k + 1 : ℕ) : ℝ)) • C := by rw [add_smul]
    _ = ((k + 2 : ℕ) : ℝ) • C := by
      congr 1
      push_cast
      ring

end
end QuaternionicSymmetry.LocalChernWeilOrderedNormalization
