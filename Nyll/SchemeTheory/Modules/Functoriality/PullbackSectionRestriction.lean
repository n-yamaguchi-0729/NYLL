/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Functoriality.QuasicoherentPullbackSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual restriction of affine pullback sections

The original unit commutes with simultaneous restriction of the source
and target opens. On affine opens, the actual pullback equivalence
therefore sends restriction of either original factor to the original
restriction of the corresponding pure tensor section.

This formula uses the actual two section rings at each open. It does not
choose an identification between coefficient rings belonging to different
opens, and applies to any subordinate pair of affine opens.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- The original restricted unit commutes with simultaneous restriction
of both opens in an actual subordinate square. -/
theorem pullbackUnitSections_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) {U U' : Y.Opens} {V V' : X.Opens}
    (iU : U' ⟶ U) (iV : V' ⟶ V) (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U')
    (x : Γ(M, U)) :
    ((pullback f).obj M).presheaf.map iV.op ((pullbackUnitSections f U V h).app M x) =
      (pullbackUnitSections f U' V' h').app M (M.presheaf.map iU.op x) := by
  let N : X.Modules := (pullback f).obj M
  let a : V ⟶ f ⁻¹ᵁ U := homOfLE h
  let b : V' ⟶ f ⁻¹ᵁ U' := homOfLE h'
  let k : f ⁻¹ᵁ U' ⟶ f ⁻¹ᵁ U := (TopologicalSpace.Opens.map f.base).map iU
  let z : Γ(N, f ⁻¹ᵁ U) := pullbackLocalSection f x
  have hc : a.op ≫ iV.op = k.op ≫ b.op := Subsingleton.elim _ _
  have hdiag : N.presheaf.map a.op ≫ N.presheaf.map iV.op =
      N.presheaf.map k.op ≫ N.presheaf.map b.op :=
    (N.presheaf.map_comp a.op iV.op).symm.trans
      ((congrArg (fun l : op (f ⁻¹ᵁ U) ⟶ op V' => N.presheaf.map l) hc).trans
        (N.presheaf.map_comp k.op b.op))
  have h₁ := congrArg (fun l : Γ(N, f ⁻¹ᵁ U) ⟶ Γ(N, V') => l z) hdiag
  have h₂ := congrArg (fun y : Γ(N, f ⁻¹ᵁ U') => N.presheaf.map b.op y)
    (map_pullbackLocalSection f iU x)
  exact h₁.trans h₂

/-- The affine pullback equivalence respects the original restrictions
of both pure tensor factors along a pair of subordinate affine opens. -/
theorem affinePullbackSectionsEquiv_restriction_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] {U U' : Y.Opens} {V V' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (iU : U' ⟶ U) (iV : V' ⟶ V) (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U')
    (s : Γ(X, V)) (x : Γ(M, U)) :
    ((pullback f).obj M).presheaf.map iV.op
        (affinePullbackSectionsEquiv f U V hU hV h M
          (s ⊗ₜ[Γ(Y, U),(f.appLE U V h).hom] x)) =
      affinePullbackSectionsEquiv f U' V' hU' hV' h' M
        (X.presheaf.map iV.op s ⊗ₜ[Γ(Y, U'),(f.appLE U' V' h').hom]
          M.presheaf.map iU.op x) := by
  let N : X.Modules := (pullback f).obj M
  let y : Γ(N, V) := (pullbackUnitSections f U V h).app M x
  let r : Γ(X, V') := X.presheaf.map iV.op s
  have h₁ := congrArg (fun z : Γ(N, V) => N.presheaf.map iV.op z)
    (affinePullbackSectionsEquiv_tmul f U V hU hV h M s x)
  have h₂ := Scheme.Modules.map_smul N iV s y
  have h₃ := congrArg (fun z : Γ(N, V') => r • z)
    (pullbackUnitSections_restriction f M iU iV h h' x)
  have h₄ := affinePullbackSectionsEquiv_tmul f U' V' hU' hV' h' M r
    (M.presheaf.map iU.op x)
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

end AlgebraicGeometry.Scheme.Modules
