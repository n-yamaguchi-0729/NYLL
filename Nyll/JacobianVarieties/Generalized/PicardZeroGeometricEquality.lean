/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZero
import Nyll.SchemeTheory.Topology.FppfAlgebraicallyClosedPoint

/-! # Equality of actual rigidified classes on geometric tests -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- Equal zero-sheaf classes give equal actual rigidified classes on every geometric test. -/
theorem modulusPicardZero_raw_eq_on_geometricPoint
    {T : Over (Spec (CommRingCat.of R))}
    (x y : (modulusPicardZeroPresheaf c i).obj (op T))
    (he : (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroPresheaf c i)).app (op T) x =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroPresheaf c i)).app (op T) y)
    {L : Type u} [Field L] [IsAlgClosed L]
    {s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    (p : Over.mk s ⟶ T) :
    (modulusPicardPresheaf c i).map p.op x.val =
      (modulusPicardPresheaf c i).map p.op y.val := by
  let η := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (modulusPicardZeroPresheaf c i)
  have hx := ConcreteCategory.congr_hom (η.naturality p.op) x
  have hy := ConcreteCategory.congr_hom (η.naturality p.op) y
  have hη : η.app (op (Over.mk s)) ((modulusPicardZeroPresheaf c i).map p.op x) =
      η.app (op (Over.mk s)) ((modulusPicardZeroPresheaf c i).map p.op y) :=
    hx.trans ((congrArg ((modulusPicardZeroSheaf c i).obj.map p.op) he).trans hy.symm)
  exact congrArg Subtype.val ((Scheme.fppf_locallyBijective_app_bijective η s).injective hη)

end AlgebraicGeometry.GeneralizedJacobian
