/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.ZeroSchemeIdealCompEq

/-!
# Linear equivalence with the actual modulus normalization

Two effective divisors away from the modulus determine the same rigidified class
exactly when one is cut out by a section of the other's inverse ideal whose
restriction agrees with its canonical section on the full modulus. This is the
geometric section criterion underlying the rational-function congruence in the
modulus divisor-class comparison.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X)

/-- Equality of the actual rigidified divisor classes is equivalent to a
section cutting out the first divisor and agreeing with the second canonical
section on the entire modulus. Equality is equality of sheaf morphisms on `D`,
so nilpotents and higher-order congruences are retained. -/
theorem classOf_ofInvertibleIdeal_eq_iff (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hIa : ∀ y : D, i.base y ∉ I.support)
    (hJa : ∀ y : D, i.base y ∉ J.support) :
    classOf (ofInvertibleIdeal i I hI hIa) =
        classOf (ofInvertibleIdeal i J hJ hJa) ↔
      ∃ s : 𝟙_ X.Modules ⟶ J.invModule,
        zeroSchemeIdeal s = I ∧
        pullbackSection i s = pullbackSection i J.invModuleSection := by
  constructor
  · intro h
    obtain ⟨e⟩ := (classOf_eq_iff (ofInvertibleIdeal i I hI hIa)
      (ofInvertibleIdeal i J hJ hJa)).mp h
    let e₀ : I.invModule ≅ J.invModule := e.toIso
    refine ⟨I.invModuleSection ≫ e₀.hom, ?_, ?_⟩
    · exact (zeroSchemeIdeal_comp_eq_of_isIso I.invModuleSection e₀.hom).trans
        hI.zeroSchemeIdeal_invModuleSection
    · have hp : pullbackSection i (I.invModuleSection ≫ e.toIso.hom) =
          pullbackSection i I.invModuleSection ≫
            (Scheme.Modules.pullback i).map e.toIso.hom := by
        exact (congrArg (fun f => (pullbackUnitIso i).inv ≫ f)
          ((Scheme.Modules.pullback i).map_comp I.invModuleSection e.toIso.hom)).trans
            (CategoryTheory.Category.assoc (pullbackUnitIso i).inv
              ((Scheme.Modules.pullback i).map I.invModuleSection)
              ((Scheme.Modules.pullback i).map e.toIso.hom)).symm
      apply (cancel_mono (ofInvertibleIdeal i J hJ hJa).trivialization.hom).mp
      exact (congrArg
        (fun f => f ≫ (ofInvertibleIdeal i J hJ hJa).trivialization.hom) hp).trans
        ((Category.assoc (pullbackSection i I.invModuleSection)
          ((Scheme.Modules.pullback i).map e.toIso.hom)
          (ofInvertibleIdeal i J hJ hJa).trivialization.hom).trans
          ((congrArg (fun f => pullbackSection i I.invModuleSection ≫ f)
            e.compatible).trans
            ((ofInvertibleIdeal_section i I hI hIa).trans
              (ofInvertibleIdeal_section i J hJ hJa).symm)))
  · rintro ⟨s, hzero, hrestriction⟩
    have hs : pullbackSection i s ≫
        (ofInvertibleIdeal i J hJ hJa).trivialization.hom =
          𝟙 (𝟙_ D.Modules) := by
      rw [hrestriction]
      exact ofInvertibleIdeal_section i J hJ hJa
    exact (classOf_eq_iff (ofInvertibleIdeal i I hI hIa)
      (ofInvertibleIdeal i J hJ hJa)).mpr
        ⟨(zeroDivisorIso (ofInvertibleIdeal i J hJ hJa) s hs I hI hzero hIa).symm⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
