/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Degree.UnitriangularDivisorBound
import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexComp
import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqOrdSub
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusMultiplicativeJets

/-! # Integrality of a descended unitriangular product

An element in the base field has order divisible by the actual ramification
index after extension. A pole strictly smaller than that index is therefore
impossible. Applying the uniform unitriangular product bound gives integrality
of every entry of an actual descended product, independently of its length.
This is a boundary-integrality estimate, not a group embedding or a global
modulus-existence assertion.
-/

noncomputable section

namespace AlgebraicCurve.Place

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E]

/-- A base-field element whose extended pole is smaller than the ramification
index is integral at the restricted place. -/
theorem ord_nonneg_of_pole_lt_ramificationIndexAlong
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral) (w : Place K E) (x : F)
    (hx : -(w.ramificationIndexAlong φ : ℤ) < w.ord (φ x)) :
    0 ≤ (w.restrictAlong φ hφ).ord x := by
  rw [w.ord_restrictAlong φ hφ] at hx
  by_contra h
  have hneg : (w.restrictAlong φ hφ).ord x ≤ -1 := by omega
  have hmul := mul_le_mul_of_nonneg_left hneg
    (Int.natCast_nonneg (w.ramificationIndexAlong φ))
  rw [mul_neg_one] at hmul
  omega

/-- A unitriangular product which actually descends has integral entries
whenever its uniform product pole bound is smaller than ramification. -/
theorem ord_descended_unitriangular_product_nonneg
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral) (w : Place K E)
    {r : ℕ} (L : List (Matrix (Fin r) (Fin r) E)) (b : ℕ)
    (hL : ∀ A ∈ L, A.IsUpperTriangular)
    (hd : ∀ A ∈ L, ∀ i, A i i = 1)
    (hb : ∀ A ∈ L, ∀ i j, -(b : ℤ) ≤ w.ord (A i j))
    (hsmall : (r - 1) * b < w.ramificationIndexAlong φ)
    (B : Matrix (Fin r) (Fin r) F) (hdesc : B.map φ = L.prod)
    (i j : Fin r) : 0 ≤ (w.restrictAlong φ hφ).ord (B i j) := by
  have hprod := w.ord_list_prod_unitriangular_ge L b hL hd hb i j
  have hentry : φ (B i j) = L.prod i j := congrArg (fun A => A i j) hdesc
  apply w.ord_nonneg_of_pole_lt_ramificationIndexAlong φ hφ (B i j)
  rw [hentry]
  have hsmallZ : (((r - 1) * b : ℕ) : ℤ) < (w.ramificationIndexAlong φ : ℤ) :=
    Int.ofNat_lt.mpr hsmall
  exact lt_of_lt_of_le (neg_lt_neg hsmallZ) hprod

/-- The explicit factor bound `(e - 1) / (r - 1)` makes every entry of a
product which descends to the base field integral. Here `r > 1` and `e > 0`. -/
theorem descended_unitriangular_product_mem_of_floor_bound
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral) (w : Place K E)
    {r : ℕ} (hr : 1 < r) (he : 0 < w.ramificationIndexAlong φ)
    (L : List (Matrix (Fin r) (Fin r) E))
    (hL : ∀ A ∈ L, A.IsUpperTriangular)
    (hd : ∀ A ∈ L, ∀ i, A i i = 1)
    (hb : ∀ A ∈ L, ∀ i j,
      -(((w.ramificationIndexAlong φ - 1) / (r - 1) : ℕ) : ℤ) ≤ w.ord (A i j))
    (B : Matrix (Fin r) (Fin r) F) (hdesc : B.map φ = L.prod)
    (i j : Fin r) : B i j ∈ (w.restrictAlong φ hφ).toValuationSubring := by
  let e := w.ramificationIndexAlong φ
  let b := (e - 1) / (r - 1)
  have hdenom : 0 < r - 1 := Nat.sub_pos_of_lt hr
  have hdiv : b * (r - 1) ≤ e - 1 :=
    (Nat.le_div_iff_mul_le hdenom).mp (Nat.le_refl b)
  have hsmall : (r - 1) * b < e := by
    rw [Nat.mul_comm]
    exact lt_of_le_of_lt hdiv (Nat.sub_lt he Nat.zero_lt_one)
  exact (w.restrictAlong φ hφ).mem_toValuationSubring_of_ord_nonneg
    (w.ord_descended_unitriangular_product_nonneg φ hφ L b hL hd hb hsmall B hdesc i j)

private theorem ramificationIndexAlong_pos_of_integral
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral) (w : Place K E) :
    0 < w.ramificationIndexAlong φ := by
  let _ := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

variable {L : Type*} [Field L] [Algebra K L]

/-- Conductor-sized ramification on the curve makes a mapped entry satisfy
one uniform pole bound in the common extension, using the actual tower index. -/
theorem ord_map_ge_floor_of_ramification_tower
    (ψ : L →ₐ[K] F) (hψ : ψ.toRingHom.IsIntegral)
    (σ : F →ₐ[K] E) (hσ : σ.toRingHom.IsIntegral)
    (φ : L →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (hcomp : σ.comp ψ = φ) (w : Place K E)
    {r : ℕ} (hr : 1 < r) (b : ℕ)
    (hram : (r - 1) * b < (w.restrictAlong σ hσ).ramificationIndexAlong ψ)
    (x : F) (hx : -(b : ℤ) ≤ (w.restrictAlong σ hσ).ord x) :
    -(((w.ramificationIndexAlong φ - 1) / (r - 1) : ℕ) : ℤ) ≤ w.ord (σ x) := by
  have hσψ : (σ.comp ψ).toRingHom.IsIntegral := by
    rw [hcomp]
    exact hφ
  have htower : w.ramificationIndexAlong φ =
      w.ramificationIndexAlong σ * (w.restrictAlong σ hσ).ramificationIndexAlong ψ := by
    simpa only [hcomp] using w.ramificationIndexAlong_comp ψ σ hψ hσ hσψ
  have hpos := w.ramificationIndexAlong_pos_of_integral σ hσ
  have hsmall : (w.ramificationIndexAlong σ * b) * (r - 1) <
      w.ramificationIndexAlong φ := by
    calc
      _ = w.ramificationIndexAlong σ * ((r - 1) * b) := by ac_rfl
      _ < w.ramificationIndexAlong σ *
          (w.restrictAlong σ hσ).ramificationIndexAlong ψ :=
        Nat.mul_lt_mul_of_pos_left hram hpos
      _ = _ := htower.symm
  have hfloor : w.ramificationIndexAlong σ * b ≤
      (w.ramificationIndexAlong φ - 1) / (r - 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hr)).mpr
    omega
  have hext : -((w.ramificationIndexAlong σ * b : ℕ) : ℤ) ≤ w.ord (σ x) := by
    rw [w.ord_restrictAlong σ hσ]
    simpa only [Nat.cast_mul, mul_neg] using
      mul_le_mul_of_nonneg_left hx (Int.natCast_nonneg (w.ramificationIndexAlong σ))
  exact le_trans (neg_le_neg (Int.ofNat_le.mpr hfloor)) hext

/-- Any repeated list of embeddings gives an integral descended matrix
product when every source-place ramification dominates its entry pole bound.
The list is not converted to a set, so repeated factors retain multiplicity. -/
theorem descended_unitriangular_embedding_product_mem
    (ψ : L →ₐ[K] F) (hψ : ψ.toRingHom.IsIntegral)
    (φ : L →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral) (w : Place K E)
    {r : ℕ} (hr : 1 < r) (A : Matrix (Fin r) (Fin r) F)
    (hA : A.IsUpperTriangular) (hd : ∀ i, A i i = 1)
    (embeddings : List (F →ₐ[K] E))
    (hEmb : ∀ σ ∈ embeddings, σ.toRingHom.IsIntegral)
    (hcomp : ∀ σ ∈ embeddings, σ.comp ψ = φ)
    (b : (F →ₐ[K] E) → ℕ)
    (hb : ∀ (σ : F →ₐ[K] E) (hσ : σ ∈ embeddings), ∀ i j,
      -(b σ : ℤ) ≤ (w.restrictAlong σ (hEmb σ hσ)).ord (A i j))
    (hram : ∀ (σ : F →ₐ[K] E) (hσ : σ ∈ embeddings),
      (r - 1) * b σ < (w.restrictAlong σ (hEmb σ hσ)).ramificationIndexAlong ψ)
    (B : Matrix (Fin r) (Fin r) L)
    (hdesc : B.map φ = (embeddings.map (fun σ : F →ₐ[K] E => A.map σ)).prod)
    (i j : Fin r) : B i j ∈ (w.restrictAlong φ hφ).toValuationSubring := by
  apply w.descended_unitriangular_product_mem_of_floor_bound φ hφ hr
    (w.ramificationIndexAlong_pos_of_integral φ hφ)
    (embeddings.map (fun σ : F →ₐ[K] E => A.map σ)) ?_ ?_ ?_ B hdesc i j
  · intro M hM
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hM
    intro k l hlk
    change σ (A k l) = 0
    rw [hA hlk, map_zero]
  · intro M hM k
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hM
    change σ (A k k) = 1
    rw [hd, map_one]
  · intro M hM k l
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hM
    exact w.ord_map_ge_floor_of_ramification_tower ψ hψ σ (hEmb σ hσ) φ hφ
      (hcomp σ hσ) hr (b σ) (hram σ hσ) (A k l) (hb σ hσ k l)

/-- The actual principal-unit congruence of `ψ(X)` forces the required
ramification bound over the rational point `1`; the ramification inequality
is proved from the order of `ψ(X) - 1`, rather than assumed. -/
theorem ramificationIndexAlong_gt_of_principal_congruence
    (ψ : RatFunc K →ₐ[K] F) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F)
    (hv : v.restrictAlong ψ hψ = RationalFunctionField.placeOfPoint K 1)
    {r b n : ℕ} (hn : (r - 1) * b + 1 ≤ n)
    (hcong : v.CongruentOne n (ψ RatFunc.X)) :
    (r - 1) * b < v.ramificationIndexAlong ψ := by
  have he := v.ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint
    ψ hψ 1 hv
  rw [map_one] at he
  have hpos : (0 : ℤ) < (v.ramificationIndexAlong ψ : ℤ) :=
    Int.ofNat_lt.mpr (v.ramificationIndexAlong_pos_of_integral ψ hψ)
  have hval := (v.congruentOne_iff_adicValuation_sub_one_le (by omega) _).mp hcong
  rcases v.adicValuation_le_exp_iff.mp hval with hzero | hord
  · rw [hzero, v.ord_zero] at he
    omega
  · have hnord : (n : ℤ) ≤ (v.ramificationIndexAlong ψ : ℤ) := by
      rw [he]
      simpa only [neg_neg] using hord
    have hcut : (((r - 1) * b : ℕ) : ℤ) < (n : ℤ) :=
      Int.ofNat_lt.mpr (by omega)
    exact Int.ofNat_lt.mp (lt_of_lt_of_le hcut hnord)

/-- A full principal congruence gives integral entries of the actual descended
embedding product at the place over `1`. Only positive source pole bounds need
modulus coefficients; entries already integral require no artificial support.
All ramification inequalities are constructed inside the proof. -/
theorem descended_unitriangular_embedding_product_mem_of_principal_congruence
    (ψ : RatFunc K →ₐ[K] F) (hψ : ψ.toRingHom.IsIntegral)
    (φ : RatFunc K →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral) (w : Place K E)
    (hw : w.restrictAlong φ hφ = RationalFunctionField.placeOfPoint K 1)
    {r : ℕ} (hr : 1 < r) (A : Matrix (Fin r) (Fin r) F)
    (hA : A.IsUpperTriangular) (hd : ∀ i, A i i = 1)
    (embeddings : List (F →ₐ[K] E))
    (hEmb : ∀ σ ∈ embeddings, σ.toRingHom.IsIntegral)
    (hcomp : ∀ σ ∈ embeddings, σ.comp ψ = φ)
    (b : (F →ₐ[K] E) → ℕ)
    (hb : ∀ (σ : F →ₐ[K] E) (hσ : σ ∈ embeddings), ∀ i j,
      -(b σ : ℤ) ≤ (w.restrictAlong σ (hEmb σ hσ)).ord (A i j))
    (D : Modulus K F) (hcong : D.CongruentOne (ψ RatFunc.X))
    (hD : ∀ (σ : F →ₐ[K] E) (hσ : σ ∈ embeddings), b σ ≠ 0 →
      (r - 1) * b σ + 1 ≤ D (w.restrictAlong σ (hEmb σ hσ)))
    (B : Matrix (Fin r) (Fin r) (RatFunc K))
    (hdesc : B.map φ = (embeddings.map (fun σ : F →ₐ[K] E => A.map σ)).prod)
    (i j : Fin r) : B i j ∈ (w.restrictAlong φ hφ).toValuationSubring := by
  apply w.descended_unitriangular_embedding_product_mem ψ hψ φ hφ hr A hA hd
    embeddings hEmb hcomp b hb ?_ B hdesc i j
  intro σ hσ
  let v := w.restrictAlong σ (hEmb σ hσ)
  by_cases hbzero : b σ = 0
  · rw [hbzero, Nat.mul_zero]
    exact v.ramificationIndexAlong_pos_of_integral ψ hψ
  · have hcoeff := hD σ hσ hbzero
    have hDv : D v ≠ 0 := by
      change D (w.restrictAlong σ (hEmb σ hσ)) ≠ 0
      omega
    have hσψ : (σ.comp ψ).toRingHom.IsIntegral := by
      rw [hcomp σ hσ]
      exact hφ
    have hv : v.restrictAlong ψ hψ = RationalFunctionField.placeOfPoint K 1 := by
      have hrest : v.restrictAlong ψ hψ = w.restrictAlong φ hφ := by
        simpa only [hcomp σ hσ] using
          w.restrictAlong_restrictAlong ψ σ hψ (hEmb σ hσ) hσψ
      exact hrest.trans hw
    exact v.ramificationIndexAlong_gt_of_principal_congruence ψ hψ hv hcoeff
      (hcong.2 v hDv)

end AlgebraicCurve.Place
