/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_kw_cart_C_pow_smul_D_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Cartier.CartierFixedness
import Nyll.AlgebraicCurves.Differentials.Cartier.CartierCoordinates

/-!
# Kw cart C pow smul D eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.Kw_cart_C_pow_smul_D_eq_zero

noncomputable section

open AlgebraicCurve.PthPower AlgebraicCurve.Cartier AlgebraicCurve.CartierLogarithmic

namespace CartMintSol

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]
variable (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
  (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
  (hsep : ∀ x : F, IsSeparable (adjoinPthPowers (ℓ := ℓ) t).toSubfield x)
  (hdeg : (minpoly (pthPowers F ℓ) t).natDegree = ℓ)

private def CC : Ω[F⁄K] →+ Ω[F⁄K] :=
  AddMonoidHom.mk' (cartier (K := K) t hdt hspan hsep hdeg)
    (fun ω ω' => cartier_add t hdt hspan hsep hdeg ω ω')

private theorem CC_apply (ω : Ω[F⁄K]) :
    CC t hdt hspan hsep hdeg ω = cartier (K := K) t hdt hspan hsep hdeg ω := rfl

private theorem CC_semilinear (a : F) (ω : Ω[F⁄K]) :
    CC t hdt hspan hsep hdeg (a ^ ℓ • ω) = a • CC t hdt hspan hsep hdeg ω :=
  cartier_pow_smul t hdt hspan hsep hdeg a ω

private theorem repr_pow_basis {k : ℕ} (hk : k < ℓ) :
    powerCoefficients t hsep hdeg (t ^ k)
      = fun j : Fin ℓ => if j = ⟨k, hk⟩ then 1 else 0 := by
  refine powerCoefficients_unique t hsep hdeg ?_
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin ℓ)]
  · simp only [ite_true, OneMemClass.coe_one, one_mul]
  · intro j _ hj
    simp [hj]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

private theorem repr_pow_top_eq_zero {k : ℕ} (hk : k + 1 < ℓ) :
    powerCoefficients t hsep hdeg (t ^ k)
      ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩ = 0 := by
  have hklt : k < ℓ := by omega
  rw [repr_pow_basis t hsep hdeg hklt]
  have hne : (⟨ℓ - 1, by have := hℓ.out.pos; omega⟩ : Fin ℓ) ≠ ⟨k, hklt⟩ := by
    intro he
    have hv : ℓ - 1 = k := by injection he
    omega
  exact ite_eq_right hne

private theorem root_zero : pthRoot (0 : pthPowers F ℓ) = 0 :=
  pthRoot_unique (by simp [zero_pow hℓ.out.ne_zero])

private theorem C_pow_smul_Dt {k : ℕ} (hk : k + 1 < ℓ) :
    cartier (K := K) t hdt hspan hsep hdeg
      (t ^ k • KaehlerDifferential.D K F t) = 0 := by
  have hcoord : differentialCoordinate t hdt hspan
      (t ^ k • KaehlerDifferential.D K F t) = t ^ k :=
    differentialCoordinate_unique t hdt hspan rfl
  rw [cartier, hcoord, repr_pow_top_eq_zero t hsep hdeg hk, root_zero, zero_smul]

private theorem C_D_eq_zero (f : F) :
    cartier (K := K) t hdt hspan hsep hdeg (KaehlerDifferential.D K F f) = 0 := by
  rw [D_eq_derivativeEval_smul t hsep hdeg f, derivativeEval, Finset.sum_smul, ← CC_apply, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · simp [h0]
  · obtain ⟨w, hw⟩ := (mem_pthPowers_iff F ℓ).mp
      (powerCoefficients t hsep hdeg f i).2
    have hcast : (((i : ℕ) : F)) ^ ℓ = ((i : ℕ) : F) := natCast_pow_char (i : ℕ)
    have hsplit : ((i : ℕ) : F) * ((powerCoefficients t hsep hdeg f i : F))
        * t ^ ((i : ℕ) - 1) = (((i : ℕ) : F) * w) ^ ℓ * t ^ ((i : ℕ) - 1) := by
      rw [mul_pow, hcast, hw]
    have hlt : ((i : ℕ) - 1) + 1 < ℓ := by
      have h2 := i.isLt
      omega
    rw [hsplit, mul_smul, CC_semilinear, CC_apply,
      C_pow_smul_Dt t hdt hspan hsep hdeg hlt, smul_zero]

private theorem C_pow_pred_smul_D (g : F) :
    cartier (K := K) t hdt hspan hsep hdeg
      (g ^ (ℓ - 1) • KaehlerDifferential.D K F g) = KaehlerDifferential.D K F g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, smul_zero, ← CC_apply, map_zero]
  · obtain ⟨q, rfl⟩ : ∃ q, ℓ = q + 1 :=
      ⟨ℓ - 1, by have := hℓ.out.one_lt; omega⟩
    rw [Nat.add_sub_cancel]
    have hkey : g ^ q • KaehlerDifferential.D K F g
        = g ^ (q + 1) • (g⁻¹ • KaehlerDifferential.D K F g) := by
      rw [smul_smul, pow_succ, mul_assoc, mul_inv_cancel₀ hg, mul_one]
    have hfix := cartier_dlog (K := K) t hdt hspan hsep hdeg hg
    rw [AlgebraicCurve.dlog] at hfix
    rw [hkey, cartier_pow_smul, hfix, smul_smul, mul_inv_cancel₀ hg, one_smul]

private theorem C_dlog_fixed_all (g : F) :
    cartier (K := K) t hdt hspan hsep hdeg
      (g⁻¹ • KaehlerDifferential.D K F g) = g⁻¹ • KaehlerDifferential.D K F g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, smul_zero, ← CC_apply, map_zero]
  · have h := cartier_dlog (K := K) t hdt hspan hsep hdeg hg
    simpa only [AlgebraicCurve.dlog] using h

private theorem C_pow_smul_D_eq_zero (g : F) {i : ℕ} (hi : i + 1 < ℓ) :
    cartier (K := K) t hdt hspan hsep hdeg
      (g ^ i • KaehlerDifferential.D K F g) = 0 := by
  have hne : ((i + 1 : ℕ) : F) ≠ 0 := by
    intro h0
    have hdvd := (CharP.cast_eq_zero_iff F ℓ (i + 1)).1 h0
    exact absurd (Nat.le_of_dvd (Nat.succ_pos i) hdvd) (not_le.2 hi)
  have hleib : KaehlerDifferential.D K F (g ^ (i + 1))
      = ((i + 1 : ℕ) : F) • (g ^ i • KaehlerDifferential.D K F g) := by
    rw [(KaehlerDifferential.D K F).leibniz_pow g (i + 1), Nat.add_sub_cancel,
      Nat.cast_smul_eq_nsmul]
  have hcp : (((i + 1 : ℕ) : F)⁻¹) ^ ℓ = ((i + 1 : ℕ) : F)⁻¹ := by
    rw [inv_pow, ← frobenius_def, map_natCast]
  have hrew : g ^ i • KaehlerDifferential.D K F g
      = (((i + 1 : ℕ) : F)⁻¹) ^ ℓ • KaehlerDifferential.D K F (g ^ (i + 1)) := by
    rw [hcp, hleib, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrew, cartier_pow_smul, C_D_eq_zero t hdt hspan hsep hdeg, smul_zero]

private theorem C_digits (g : F) (a : Fin ℓ → F) :
    cartier (K := K) t hdt hspan hsep hdeg
      ((∑ i : Fin ℓ, a i ^ ℓ * g ^ (i : ℕ)) • KaehlerDifferential.D K F g) =
      a ⟨ℓ - 1, Nat.sub_lt (Fact.out : ℓ.Prime).pos Nat.one_pos⟩ •
        KaehlerDifferential.D K F g := by
  have hp : ℓ.Prime := Fact.out
  rw [Finset.sum_smul, ← CC_apply, map_sum,
    Finset.sum_eq_single (⟨ℓ - 1, Nat.sub_lt hp.pos Nat.one_pos⟩ : Fin ℓ)]
  · rw [mul_smul, CC_semilinear, CC_apply, C_pow_pred_smul_D t hdt hspan hsep hdeg g]
  · intro i _ hi
    have hi' : (i : ℕ) ≠ ℓ - 1 := fun h => hi (Fin.ext h)
    have hlt : (i : ℕ) + 1 < ℓ := by
      have := i.isLt
      omega
    rw [mul_smul, CC_semilinear, CC_apply,
      C_pow_smul_D_eq_zero t hdt hspan hsep hdeg g hlt, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end CartMintSol

theorem _root_.AlgebraicCurve.cartier_pow_smul_D_eq_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F,
      IsSeparable (AlgebraicCurve.PthPower.adjoinPthPowers (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (AlgebraicCurve.PthPower.pthPowers F ℓ) t).natDegree = ℓ)
    (g : F) {i : ℕ} (hi : i + 1 < ℓ) :
    AlgebraicCurve.Cartier.cartier (K := K) t hdt hspan hsep hdeg
      (g ^ i • KaehlerDifferential.D K F g) = 0 :=
  CartMintSol.C_pow_smul_D_eq_zero t hdt hspan hsep hdeg g hi
end
end AlgebraicCurves.Differentials.Proofs.Kw_cart_C_pow_smul_D_eq_zero
end ProofImplementation

attribute [-simp] AlgebraicCurve.CartierLogarithmic.coe_pthPower AlgebraicCurve.dlog_zero
  AlgebraicCurve.mem_regularDifferentialsOfNonnegativeOrder_iff AlgebraicCurve.dlog_one
