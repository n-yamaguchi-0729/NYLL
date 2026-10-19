/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Sections.AffineRestriction
import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Original unit sections on the canonical affine chart

The linear comparison for the canonical affine restriction sends its
actual restricted unit section back to the original section. Composing
with the original restriction-to-pullback isomorphism gives the same
statement for genuine scheme pullback along the canonical affine chart.

This supplies the precise unit compatibility needed to transport the
spectrum pullback section theorem to arbitrary affine opens.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_pullbackLocalSection

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

/-- The linear affine restriction comparison recovers the original
section from its actual restriction unit on the canonical spectrum. -/
theorem affineRestrictionSectionsEquiv_unit (M : X.Modules) (x : Γ(M, U)) :
    affineRestrictionSectionsEquiv U hU M
        ((M.restrict hU.fromSpec).presheaf.map
          (eqToHom hU.fromSpec_preimage_self.symm).op
          (((restrictAdjunction hU.fromSpec).unit.app M).app U x)) = x := by
  let R : CommRingCat.{u} := Γ(X, U)
  let j : Spec R ⟶ X := hU.fromSpec
  let V : (Spec R).Opens := j ⁻¹ᵁ U
  let i : (⊤ : (Spec R).Opens) ⟶ V := eqToHom hU.fromSpec_preimage_self.symm
  let hImage : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let a : j ''ᵁ V ⟶ U := homOfLE (j.image_preimage_le U)
  let b : j ''ᵁ ⊤ ⟶ j ''ᵁ V := homOfLE (j.image_mono (leOfHom i))
  let c : U ⟶ j ''ᵁ ⊤ := eqToHom hImage.symm
  let η : Γ(M, U) ⟶ Γ(M.restrict j, V) := ((restrictAdjunction j).unit.app M).app U
  have h₁ := affineRestrictionSectionsEquiv_apply U hU M
    ((M.restrict j).presheaf.map i.op (η x))
  have hn := congrArg (fun k : Γ(M.restrict j, V) ⟶ Γ(M, j ''ᵁ ⊤) => k (η x))
    (M.map_restrictAppIso_hom j i.op)
  have h₂ := congrArg (fun z : Γ(M, j ''ᵁ ⊤) => M.presheaf.map c.op z) hn
  have hη : (M.restrictAppIso j V).hom (η x) = M.presheaf.map a.op x := rfl
  have h₃ := congrArg
    (fun z : Γ(M, j ''ᵁ V) => M.presheaf.map c.op (M.presheaf.map b.op z)) hη
  have hc : M.presheaf.map a.op ≫ M.presheaf.map b.op ≫ M.presheaf.map c.op =
      𝟙 Γ(M, U) := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp,
      Subsingleton.elim ((a.op ≫ b.op) ≫ c.op) (𝟙 _), CategoryTheory.Functor.map_id]
  have h₄ := congrArg (fun k : Γ(M, U) ⟶ Γ(M, U) => k x) hc
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Actual global sections of the pullback along the canonical affine
chart are linearly equivalent to the original affine sections. -/
def affineChartPullbackSectionsEquiv (M : X.Modules) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj ((pullback hU.fromSpec).obj M) ≃ₗ[Γ(X, U)]
      Γ(M, U) :=
  (((moduleSpecΓFunctor (R := Γ(X, U))).mapIso
    ((restrictFunctorIsoPullback hU.fromSpec).app M).symm).toLinearEquiv).trans
      (affineRestrictionSectionsEquiv U hU M)

/-- The affine chart pullback comparison recovers the original section
from the original pullback unit, restricted to the whole spectrum. -/
theorem affineChartPullbackSectionsEquiv_unit (M : X.Modules) (x : Γ(M, U)) :
    affineChartPullbackSectionsEquiv U hU M
        ((pullbackUnitSections hU.fromSpec U ⊤ hU.fromSpec_preimage_self.ge).app M x) = x := by
  let R : CommRingCat.{u} := Γ(X, U)
  let j : Spec R ⟶ X := hU.fromSpec
  let i : (⊤ : (Spec R).Opens) ⟶ j ⁻¹ᵁ U := eqToHom hU.fromSpec_preimage_self.symm
  let P : (Spec R).Modules := M.restrict j
  let Q : (Spec R).Modules := (pullback j).obj M
  let e : P ≅ Q := (restrictFunctorIsoPullback j).app M
  let η : Γ(M, U) ⟶ Γ(P, j ⁻¹ᵁ U) := ((restrictAdjunction j).unit.app M).app U
  have hn := congrArg (fun k : Γ(Q, j ⁻¹ᵁ U) ⟶ Γ(P, ⊤) =>
    k (pullbackLocalSection j x)) (e.inv.mapPresheaf.naturality i.op)
  have hu := PicTanH.pullbackLocalSection_openImmersion j M U x
  have hc := congrArg (fun k : P ⟶ P => k.app (j ⁻¹ᵁ U) (η x)) e.hom_inv_id
  have hi : e.inv.app (j ⁻¹ᵁ U) (pullbackLocalSection j x) = η x :=
    (congrArg (fun z : Γ(Q, j ⁻¹ᵁ U) => e.inv.app (j ⁻¹ᵁ U) z) hu).trans hc
  have hr := congrArg (fun z : Γ(P, j ⁻¹ᵁ U) => P.presheaf.map i.op z) hi
  have h := congrArg (fun z : Γ(P, ⊤) => affineRestrictionSectionsEquiv U hU M z)
    (hn.trans hr)
  exact h.trans (affineRestrictionSectionsEquiv_unit U hU M x)

/-- The inverse affine chart comparison is the literal original
pullback unit with its actual restriction to the whole spectrum. -/
theorem affineChartPullbackSectionsEquiv_symm_apply (M : X.Modules) (x : Γ(M, U)) :
    (affineChartPullbackSectionsEquiv U hU M).symm x =
      (pullbackUnitSections hU.fromSpec U ⊤ hU.fromSpec_preimage_self.ge).app M x := by
  apply (affineChartPullbackSectionsEquiv U hU M).injective
  exact ((affineChartPullbackSectionsEquiv U hU M).apply_symm_apply x).trans
    (affineChartPullbackSectionsEquiv_unit U hU M x).symm

end AlgebraicGeometry.Scheme.Modules
