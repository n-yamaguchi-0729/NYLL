/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.LinearSyzygyQuotientEquiv
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingChartSyzygyDivisibility
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The reduced principal lifting algebra on a selected chart

After killing the lifting parameter, the original relations become coefficient
relations and the remaining equations become linear syzygies. Their exact
compatibility follows from the original strictly-standard data after localizing
the original relation quotient. This gives an actual polynomial algebra
equivalence and retains both the coefficient map and the selected variables.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

/-- The actual reduced full lifting algebra, localized at the chosen parameter,
is a polynomial algebra over the corresponding localized original relation
quotient. All coefficient compatibility and comparison maps are constructed. -/
theorem exists_principalLifting_reduced_polynomial_equiv
    {R n m k κ : Type*} [CommRing R] [Finite n] [Fintype m] [DecidableEq m]
    [Fintype κ] [DecidableEq κ] (π : R)
    {B : Type*} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Algebra.Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hP : ∀ j, P.relation j = map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j))
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ l, H s j l * f l + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det)) :
    let I₀ : Ideal (MvPolynomial n R) := Ideal.span (Set.range f) ⊔ Ideal.span {C π}
    let C₀ := MvPolynomial n R ⧸ I₀
    let S := Localization.Away (Ideal.Quotient.mk I₀ (A t))
    let J₀ : Ideal (MvPolynomial (n ⊕ m) R) :=
      principalLiftingIdeal π f A H g ⊔ Ideal.span {C π}
    let D₀ := MvPolynomial (n ⊕ m) R ⧸ J₀
    let E := Localization.Away (Ideal.Quotient.mk J₀ (rename Sum.inl (A t)))
    ∃ (α : S →ₐ[R] E) (e : E ≃ₐ[R] MvPolynomial κ S),
      (∀ s, e (α s) = C s) ∧
      (∀ p : MvPolynomial n R,
        α (algebraMap C₀ S (Ideal.Quotient.mk I₀ p)) =
          algebraMap D₀ E (Ideal.Quotient.mk J₀ (rename Sum.inl p))) ∧
      ∀ i, e (algebraMap D₀ E (Ideal.Quotient.mk J₀ (X (Sum.inr (a i))))) = X i := by
  intro I₀ C₀ S J₀ D₀ E
  let q₀ : MvPolynomial n R →ₐ[R] C₀ := Ideal.Quotient.mkₐ R I₀
  let η : MvPolynomial n R →ₐ[R] S := (IsScalarTower.toAlgHom R C₀ S).comp q₀
  have hηf (j : m) : η (f j) = 0 := by
    have hj : q₀ (f j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span (Set.range f) ≤ I₀ from le_sup_left)
        (Ideal.subset_span ⟨j, rfl⟩))
    change algebraMap C₀ S (q₀ (f j)) = 0
    rw [hj, map_zero]
  have hηπ : η (C π) = 0 := by
    have hπ : q₀ (C π) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {C π} ≤ I₀ from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _)))
    change algebraMap C₀ S (q₀ (C π)) = 0
    rw [hπ, map_zero]
  have hK : Ideal.span (Set.range fun i => f (a i)) ⊔ Ideal.span {C (π ^ 2)} ≤
      RingHom.ker η.toRingHom := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hηf (a i)
    · apply Ideal.span_le.mpr
      rintro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change η (C (π ^ 2)) = 0
      rw [map_pow, map_pow, hηπ, zero_pow (by decide)]
  let A' : k → S := fun s => η (A s)
  let H' : k → m → m → S := fun s j l => η (H s j l)
  have hA : IsUnit (A' t) :=
    IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I₀ (A t))
  have hcross (s : k) (j l : m) :
      A' s * H' t j l - ∑ r, H' s j r * H' t r l = 0 := by
    apply (hA.pow 2).mul_right_eq_zero.mp
    have hz : η ((A t) ^ 2 *
        (A s * H t j l - ∑ r, H s j r * H t r l)) = 0 :=
      hK (sq_mul_crossCoefficient_mem_selected_sup_principalSquare
        π P f hP A H g hrel t a ha hsupport hminor s j l)
    simpa only [A', H', map_mul, map_pow, map_sub, map_sum] using hz
  have hdiag' (i : κ) (l : m) : H' t (a i) l = if l = a i then A' t else 0 := by
    change η (H t (a i) l) = if l = a i then η (A t) else 0
    rw [hdiag]
    by_cases hl : l = a i
    · rw [ite_eq_left hl, ite_eq_left hl]
    · rw [ite_eq_right hl, ite_eq_right hl, map_zero]
  have hsupport' (j l : m) (hl : l ∉ Set.range a) : H' t j l = 0 := by
    change η (H t j l) = 0
    rw [hsupport j l hl, map_zero]
  let K := Ideal.span (Set.range fun p : k × m => linearSyzygyRelation A' H' p.1 p.2)
  let Z := MvPolynomial m S ⧸ K
  let qZ : MvPolynomial m S →ₐ[S] Z := Ideal.Quotient.mkₐ S K
  let cZ : S →ₐ[R] Z := IsScalarTower.toAlgHom R S Z
  have hqC (s : S) : qZ (C s) = cZ s := qZ.commutes s
  obtain ⟨eLin, hselected, _⟩ :=
    exists_linearSyzygy_quotient_equiv A' H' t a ha hA hdiag' hsupport' hcross
  let values : n ⊕ m → Z :=
    Sum.elim (fun i => cZ (η (X i))) (fun j => qZ (X j))
  let φ : MvPolynomial (n ⊕ m) R →ₐ[R] Z := aeval values
  have hφinl (i : n) : φ (X (Sum.inl i)) = cZ (η (X i)) := aeval_X values _
  have hφinr (j : m) : φ (X (Sum.inr j)) = qZ (X j) := aeval_X values _
  have hφrename (p : MvPolynomial n R) : φ (rename Sum.inl p) = cZ (η p) := by
    have heq : φ.comp (rename Sum.inl) = cZ.comp η := by
      apply algHom_ext
      intro i
      change φ (rename Sum.inl (X i)) = cZ (η (X i))
      rw [rename_X, hφinl]
    exact congrArg (fun v : MvPolynomial n R →ₐ[R] Z => v p) heq
  have hφπ : φ (C π) = 0 := by
    have hh := hφrename (C π)
    rw [rename_C, hηπ, map_zero] at hh
    exact hh
  have hφrel (j : m) : φ (principalLiftingRelation π f j) = 0 := by
    rw [principalLiftingRelation, map_sub, hφrename, hηf, map_zero,
      map_mul, hφπ, zero_mul, sub_self]
  have hφsyzygy (s : k) (j : m) : φ (principalLiftingSyzygy π A H g s j) = 0 := by
    have hz : qZ (linearSyzygyRelation A' H' s j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(s, j), rfl⟩)
    have heq : φ (principalLiftingSyzygy π A H g s j) =
        qZ (linearSyzygyRelation A' H' s j) := by
      simp only [principalLiftingSyzygy, linearSyzygyRelation, map_sub, map_mul,
        map_sum, hφrename, hφinr, hφπ, zero_mul, sub_zero, hqC, A', H']
    exact heq.trans hz
  have hJφ : J₀ ≤ RingHom.ker φ.toRingHom := by
    apply sup_le
    · apply sup_le
      · apply Ideal.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact hφrel j
      · apply Ideal.span_le.mpr
        rintro _ ⟨⟨s, j⟩, rfl⟩
        exact hφsyzygy s j
    · apply Ideal.span_le.mpr
      rintro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hφπ
  let qD : MvPolynomial (n ⊕ m) R →ₐ[R] D₀ := Ideal.Quotient.mkₐ R J₀
  let lD : D₀ →ₐ[R] E := IsScalarTower.toAlgHom R D₀ E
  let δ : MvPolynomial (n ⊕ m) R →ₐ[R] E := lD.comp qD
  let βZ : D₀ →ₐ[R] Z := Ideal.Quotient.liftₐ J₀ φ (fun p hp => hJφ hp)
  have hβZ (p : MvPolynomial (n ⊕ m) R) : βZ (qD p) = φ p := rfl
  have hβA : IsUnit (βZ (Ideal.Quotient.mk J₀ (rename Sum.inl (A t)))) := by
    change IsUnit (βZ (qD (rename Sum.inl (A t))))
    rw [hβZ, hφrename]
    exact hA.map cZ.toMonoidHom
  let F : E →ₐ[R] Z :=
    IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk J₀ (rename Sum.inl (A t))) hβA
  have hF (x : D₀) : F (lD x) = βZ x :=
    IsLocalization.Away.lift_eq (Ideal.Quotient.mk J₀ (rename Sum.inl (A t))) hβA x
  have hδπ : δ (C π) = 0 := by
    have hh : qD (C π) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {C π} ≤ J₀ from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _)))
    change lD (qD (C π)) = 0
    rw [hh, map_zero]
  have hδrel (j : m) : δ (principalLiftingRelation π f j) = 0 := by
    have hh : qD (principalLiftingRelation π f j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ideal.span (Set.range (principalLiftingRelation π f)) ≤ J₀ from
          le_trans le_sup_left le_sup_left) (Ideal.subset_span ⟨j, rfl⟩))
    change lD (qD (principalLiftingRelation π f j)) = 0
    rw [hh, map_zero]
  have hδsyzygy (s : k) (j : m) : δ (principalLiftingSyzygy π A H g s j) = 0 := by
    have hh : qD (principalLiftingSyzygy π A H g s j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ideal.span (Set.range fun p : k × m =>
            principalLiftingSyzygy π A H g p.1 p.2) ≤ J₀ from
          le_trans le_sup_right le_sup_left) (Ideal.subset_span ⟨(s, j), rfl⟩))
    change lD (qD (principalLiftingSyzygy π A H g s j)) = 0
    rw [hh, map_zero]
  let ψ : MvPolynomial n R →ₐ[R] E := δ.comp (rename Sum.inl)
  have hψf (j : m) : ψ (f j) = 0 := by
    have hh := hδrel j
    rw [principalLiftingRelation, map_sub, map_mul, hδπ, zero_mul, sub_zero] at hh
    exact hh
  have hψπ : ψ (C π) = 0 := by
    change δ (rename Sum.inl (C π)) = 0
    rw [rename_C, hδπ]
  have hIψ : I₀ ≤ RingHom.ker ψ.toRingHom := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hψf j
    · apply Ideal.span_le.mpr
      rintro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hψπ
  let α₀ : C₀ →ₐ[R] E := Ideal.Quotient.liftₐ I₀ ψ (fun p hp => hIψ hp)
  have hα₀ (p : MvPolynomial n R) : α₀ (q₀ p) = δ (rename Sum.inl p) := rfl
  have hαA : IsUnit (α₀ (Ideal.Quotient.mk I₀ (A t))) := by
    change IsUnit (α₀ (q₀ (A t)))
    rw [hα₀]
    exact IsLocalization.Away.algebraMap_isUnit
      (Ideal.Quotient.mk J₀ (rename Sum.inl (A t)))
  let α : S →ₐ[R] E :=
    IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk I₀ (A t)) hαA
  have hαη (p : MvPolynomial n R) : α (η p) = δ (rename Sum.inl p) := by
    change α (algebraMap C₀ S (q₀ p)) = δ (rename Sum.inl p)
    have hlift : α (algebraMap C₀ S (q₀ p)) = α₀ (q₀ p) :=
      IsLocalization.Away.lift_eq (Ideal.Quotient.mk I₀ (A t)) hαA (q₀ p)
    exact hlift.trans (hα₀ p)
  let ζ : m → E := fun j => δ (X (Sum.inr j))
  let θ : MvPolynomial m S →ₐ[R] E := aevalTower α ζ
  have hθ (s : k) (j : m) : θ (linearSyzygyRelation A' H' s j) = 0 := by
    have hh := hδsyzygy s j
    simp only [principalLiftingSyzygy, map_sub, map_mul, map_sum, hδπ,
      zero_mul, sub_zero] at hh
    simpa only [θ, linearSyzygyRelation, map_sub, map_mul, map_sum,
      aevalTower_C, aevalTower_X, A', H', hαη, ζ] using hh
  let G : Z →ₐ[R] E := Ideal.Quotient.liftₐ K θ (by
    change K ≤ RingHom.ker θ.toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, j⟩, rfl⟩
    exact hθ s j)
  have hG (p : MvPolynomial m S) : G (qZ p) = θ p := rfl
  have hFα : F.comp α = cZ := by
    apply IsLocalization.algHom_ext (.powers (Ideal.Quotient.mk I₀ (A t)))
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro p
    change F (α (η p)) = cZ (η p)
    rw [hαη]
    change F (lD (qD (rename Sum.inl p))) = cZ (η p)
    rw [hF, hβZ, hφrename]
  have hFG : F.comp G = AlgHom.id R Z := by
    apply Ideal.Quotient.algHom_ext
    apply algHom_ext'
    · apply AlgHom.ext
      intro s
      change F (G (qZ (C s))) = qZ (C s)
      rw [hG, show θ (C s) = α s from aevalTower_C α ζ s, hqC]
      exact congrArg (fun v : S →ₐ[R] Z => v s) hFα
    · intro j
      change F (G (qZ (X j))) = qZ (X j)
      rw [hG, show θ (X j) = ζ j from aevalTower_X α ζ j]
      change F (lD (qD (X (Sum.inr j)))) = qZ (X j)
      rw [hF, hβZ, hφinr]
  have hGF : G.comp F = AlgHom.id R E := by
    apply IsLocalization.algHom_ext
      (.powers (Ideal.Quotient.mk J₀ (rename Sum.inl (A t))))
    apply Ideal.Quotient.algHom_ext
    apply algHom_ext
    intro j
    change G (F (lD (qD (X j)))) = lD (qD (X j))
    rw [hF, hβZ]
    cases j with
    | inl i =>
      rw [hφinl, ← hqC, hG]
      rw [show θ (C (η (X i))) = α (η (X i)) from aevalTower_C α ζ _, hαη]
      rw [rename_X]
      rfl
    | inr j =>
      rw [hφinr, hG]
      exact aevalTower_X α ζ j
  let e : E ≃ₐ[R] MvPolynomial κ S :=
    (AlgEquiv.ofAlgHom F G hFG hGF).trans (eLin.restrictScalars R)
  refine ⟨α, e, ?_, hαη, ?_⟩
  · intro s
    change eLin (F (α s)) = C s
    rw [show F (α s) = cZ s from congrArg (fun v : S →ₐ[R] Z => v s) hFα]
    exact eLin.commutes s
  · intro i
    change eLin (F (lD (qD (X (Sum.inr (a i)))))) = X i
    rw [hF, hβZ, hφinr]
    exact hselected i

end MvPolynomial
