/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusRestriction
import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.IsoBaseChangeHomIsAffineHom

/-!
# Base change of the modulus restriction bundle

The finite pushforward of a line bundle on the full modulus commutes with
arbitrary changes of the parameter scheme. The comparison is the canonical
base change map followed by the pullback composition comparisons; no
flatness assumption on the change of parameter is required.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {C S T T' : Scheme.{u}} {c : C ⟶ S} {t : T ⟶ S} {t' : T' ⟶ S}
  {d : ℕ}

/-- Restriction to the divisor and finite pushforward commute with arbitrary
base change, for the actual pulled back divisor ideal. -/
def modulusSectionsPullbackIso (D : RelEffCartierDiv c d t)
    (L : (pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L)
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    (Scheme.Modules.pullback f).obj (modulusSections D L) ≅
      modulusSections (D.pullbackAlong f hf)
        ((Scheme.Modules.pullback (mapOnProdOver c f hf)).obj L) := by
  let g := comapSubschemeMapOver D.I f hf
  let q := D.I.subschemeι ≫ pullback.snd c t
  let q' := (D.pullbackAlong f hf).I.subschemeι ≫ pullback.snd c t'
  let N := (Scheme.Modules.pullback D.I.subschemeι).obj L
  have _ : IsFinite q := D.isFinite
  have hc : IsPullback g q' q f := isPullback_comap_snd_over D.I f hf
  have hβ : IsIso (Scheme.Modules.baseChangeHom hc.w N) :=
    Scheme.Modules.isIso_baseChangeHom_of_isAffineHom hc N
      (hL.pullback D.I.subschemeι).exists_trivialization
  let hi : g ≫ D.I.subschemeι =
      (D.pullbackAlong f hf).I.subschemeι ≫ mapOnProdOver c f hf :=
    (isPullback_comapSubschemeMapOver D.I f hf).w
  let e : (Scheme.Modules.pullback g).obj N ≅
      (Scheme.Modules.pullback (D.pullbackAlong f hf).I.subschemeι).obj
        ((Scheme.Modules.pullback (mapOnProdOver c f hf)).obj L) :=
    (Scheme.Modules.pullbackComp g D.I.subschemeι).app L ≪≫
      (Scheme.Modules.pullbackCongr hi).app L ≪≫
        ((Scheme.Modules.pullbackComp (D.pullbackAlong f hf).I.subschemeι
          (mapOnProdOver c f hf)).app L).symm
  exact @asIso _ _ _ _ (Scheme.Modules.baseChangeHom hc.w N) hβ ≪≫
    (Scheme.Modules.pushforward q').mapIso e

end AlgebraicGeometry.GeneralizedJacobian
