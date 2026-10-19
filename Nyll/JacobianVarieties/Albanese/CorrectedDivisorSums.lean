/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.SupportedDivisorSums
import Nyll.JacobianVarieties.Albanese.FiniteSums

/-! # Actual divisor-sum morphisms corrected by their degree -/

noncomputable section

universe u w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

variable {K : Type u} [Field K] {C B Y : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (U : C.Opens) {n : ℕ}
  {y : Y ⟶ Spec (CommRingCat.of K)}
  {E : RelEffCartierDiv (U.ι ≫ c) n y} (hE : E.IsUniversal)
  {b : B ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K b)
  (sum : SchemeHomOver y b) (qε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) b)

/-- The regular divisor sum minus its degree times the specified basepoint image. -/
def correctedSupportedDivisorSum {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (A : RelEffCartierDiv c n t) (hA : A.SupportedIn U) : SchemeHomOver t b :=
  G.mul t (supportedDivisorSum c U hE sum A hA)
    (G.inv t (G.sumList t (List.replicate n
      (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) qε))))

private theorem pullback_inv {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (f : T' ⟶ T) (hf : f ≫ t = t')
    (x : SchemeHomOver t b) :
    GoodReductionJacobian.schemeHomOverComp f hf (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp f hf x) := by
  let : Group (SchemeHomOver t b) := G.pointGroup t
  let : Group (SchemeHomOver t' b) := G.pointGroup t'
  let H : SchemeHomOver t b →* SchemeHomOver t' b :=
    { toFun := GoodReductionJacobian.schemeHomOverComp f hf
      map_one' := G.one_natural t t' f hf
      map_mul' := G.mul_natural t t' f hf }
  exact H.map_inv x

/-- Corrected regular sums retain arbitrary parameter-change naturality. -/
theorem correctedSupportedDivisorSum_naturality
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)}
    (A : RelEffCartierDiv c n t) (hA : A.SupportedIn U)
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp f hf
        (correctedSupportedDivisorSum c U hE G sum qε A hA) =
      correctedSupportedDivisorSum c U hE G sum qε
        (A.pullbackAlong f hf) (hA.pullbackAlong f hf) := by
  have hq : GoodReductionJacobian.schemeHomOverComp f hf
      (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) qε) =
      GoodReductionJacobian.schemeHomOverComp t' (Category.comp_id t') qε := by
    apply Subtype.ext
    change f ≫ (t ≫ qε.1) = t' ≫ qε.1
    rw [← Category.assoc, hf]
  rw [correctedSupportedDivisorSum, G.mul_natural,
    supportedDivisorSum_naturality, pullback_inv, G.sumList_natural,
    List.map_replicate, hq]
  rfl

private theorem value_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    {A : Type w} [AddCommGroup A] (v : SchemeHomOver t b → A)
    (h₁ : v (G.one t) = 0) (h₂ : ∀ x z, v (G.mul t x z) = v x + v z)
    (x : SchemeHomOver t b) : v (G.inv t x) = -v x := by
  apply eq_neg_of_add_eq_zero_left
  rw [← h₂, G.inv_mul_cancel, h₁]

private theorem value_sumList_replicate {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    {A : Type w} [AddCommGroup A] (v : SchemeHomOver t b → A)
    (h₁ : v (G.one t) = 0) (h₂ : ∀ x z, v (G.mul t x z) = v x + v z)
    (x : SchemeHomOver t b) (m : ℕ) : v (G.sumList t (List.replicate m x)) = m • v x := by
  induction m with
  | zero => rw [List.replicate_zero, RelativeGroupLaw.sumList_nil, h₁, zero_nsmul]
  | succ m ih =>
      rw [List.replicate_succ, RelativeGroupLaw.sumList_cons, h₂, ih, succ_nsmul']

/-- Every additive evaluator reads the degree correction as subtraction. -/
theorem value_correctedSupportedDivisorSum {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)}
    (A : RelEffCartierDiv c n t) (hA : A.SupportedIn U)
    {V : Type w} [AddCommGroup V] (v : SchemeHomOver t b → V)
    (h₁ : v (G.one t) = 0) (h₂ : ∀ x z, v (G.mul t x z) = v x + v z) :
    v (correctedSupportedDivisorSum c U hE G sum qε A hA) =
      v (supportedDivisorSum c U hE sum A hA) -
        n • v (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) qε) := by
  rw [correctedSupportedDivisorSum, h₂, value_inv G t v h₁ h₂,
    value_sumList_replicate G t v h₁ h₂, sub_eq_add_neg]

end JacobianVarieties.Albanese
