/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.SupportedDivisorSumAdditivity
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.SchemeTheory.Sheaves.IdealSheafComap

/-! # The actual two-block trace difference

Full Cartier ideal multiplication is preserved by both base changes.
Support of the full pulled-back divisor supplies support of both blocks.
The represented divisor-sum additivity then identifies its group quotient
with the product of the two block quotients, retaining multiplicities and
working over the possibly nonreduced test scheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace JacobianVarieties.Albanese

/-- Full-ideal block decomposition computes the quotient of the two actual
pulled-back sums. In particular this applies to the reciprocal and constant
pullbacks of the Henselian regular/boundary decomposition. -/
theorem supportedDivisorSum_pullback_difference_blocks
    {K : Type u} [Field K] {C R T : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom) {m n : ℕ}
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q (m + n))
    (s₀ : OpenCurveSum c U (commGroupRelativeLaw G) q m)
    (s₁ : OpenCurveSum c U (commGroupRelativeLaw G) q n)
    {r : R ⟶ Spec (.of K)} {t : T ⟶ Spec (.of K)}
    (D : RelEffCartierDiv c (m + n) r)
    (D₀ : RelEffCartierDiv c m r) (D₁ : RelEffCartierDiv c n r)
    (hI : D.I = D₀.I * D₁.I)
    (a b : T ⟶ R) (ha : a ≫ r = t) (hb : b ≫ r = t)
    (hDa : (D.pullbackAlong a ha).SupportedIn U)
    (hDb : (D.pullbackAlong b hb).SupportedIn U) :
    ∃ (h₀a : (D₀.pullbackAlong a ha).SupportedIn U)
      (h₁a : (D₁.pullbackAlong a ha).SupportedIn U)
      (h₀b : (D₀.pullbackAlong b hb).SupportedIn U)
      (h₁b : (D₁.pullbackAlong b hb).SupportedIn U),
      commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong a ha) hDa) *
        (commGroupPointEquiv G t
          (supportedDivisorSum c U s.universal s.sum (D.pullbackAlong b hb) hDb))⁻¹ =
      (commGroupPointEquiv G t
          (supportedDivisorSum c U s₀.universal s₀.sum (D₀.pullbackAlong a ha) h₀a) *
        (commGroupPointEquiv G t
          (supportedDivisorSum c U s₀.universal s₀.sum (D₀.pullbackAlong b hb) h₀b))⁻¹) *
      (commGroupPointEquiv G t
          (supportedDivisorSum c U s₁.universal s₁.sum (D₁.pullbackAlong a ha) h₁a) *
        (commGroupPointEquiv G t
          (supportedDivisorSum c U s₁.universal s₁.sum (D₁.pullbackAlong b hb) h₁b))⁻¹) := by
  have hIa : (D.pullbackAlong a ha).I =
      (D₀.pullbackAlong a ha).I * (D₁.pullbackAlong a ha).I := by
    change D.I.comap (mapOnProdOver c a ha) =
      D₀.I.comap (mapOnProdOver c a ha) * D₁.I.comap (mapOnProdOver c a ha)
    rw [hI, Scheme.IdealSheafData.comap_mul]
  have hIb : (D.pullbackAlong b hb).I =
      (D₀.pullbackAlong b hb).I * (D₁.pullbackAlong b hb).I := by
    change D.I.comap (mapOnProdOver c b hb) =
      D₀.I.comap (mapOnProdOver c b hb) * D₁.I.comap (mapOnProdOver c b hb)
    rw [hI, Scheme.IdealSheafData.comap_mul]
  have h₀a : (D₀.pullbackAlong a ha).SupportedIn U := by
    intro x hx
    apply hDa
    rw [hIa, Scheme.IdealSheafData.support_mul]
    exact Or.inl hx
  have h₁a : (D₁.pullbackAlong a ha).SupportedIn U := by
    intro x hx
    apply hDa
    rw [hIa, Scheme.IdealSheafData.support_mul]
    exact Or.inr hx
  have h₀b : (D₀.pullbackAlong b hb).SupportedIn U := by
    intro x hx
    apply hDb
    rw [hIb, Scheme.IdealSheafData.support_mul]
    exact Or.inl hx
  have h₁b : (D₁.pullbackAlong b hb).SupportedIn U := by
    intro x hx
    apply hDb
    rw [hIb, Scheme.IdealSheafData.support_mul]
    exact Or.inr hx
  have hsumA := congrArg (commGroupPointEquiv G t)
    (supportedDivisorSum_mul c U (commGroupRelativeLaw G) q s s₀ s₁
      (D.pullbackAlong a ha) (D₀.pullbackAlong a ha) (D₁.pullbackAlong a ha)
      hDa h₀a h₁a hIa)
  have hsumB := congrArg (commGroupPointEquiv G t)
    (supportedDivisorSum_mul c U (commGroupRelativeLaw G) q s s₀ s₁
      (D.pullbackAlong b hb) (D₀.pullbackAlong b hb) (D₁.pullbackAlong b hb)
      hDb h₀b h₁b hIb)
  simp only [commGroupRelativeLaw, Equiv.apply_symm_apply] at hsumA hsumB
  refine ⟨h₀a, h₁a, h₀b, h₁b, ?_⟩
  rw [hsumA, hsumB, mul_inv_rev]
  exact (congrArg (fun z =>
    (commGroupPointEquiv G t
      (supportedDivisorSum c U s₀.universal s₀.sum (D₀.pullbackAlong a ha) h₀a) *
    commGroupPointEquiv G t
      (supportedDivisorSum c U s₁.universal s₁.sum (D₁.pullbackAlong a ha) h₁a)) * z)
      (mul_comm _ _)).trans (mul_mul_mul_comm _ _ _ _)

end JacobianVarieties.Albanese
