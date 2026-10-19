/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicPresheaf
import Nyll.SchemeTheory.WeilRestriction.RelativeTotal
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The total Poincaré frame family over the original field

Collecting the relative frame sheaf over all maps to the ordinary Picard
carrier gives a represented fppf sheaf over the original field. Its projection
to the ordinary Picard functor is the actual structure map of the same frame
scheme. Comparison with the modulus Picard-zero sheaf remains separate.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open NeronModelInfra GoodReductionJacobian SchemeTheory.WeilRestriction
open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {P : SubPicCondition c ε} {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P J)

/-- The actual Poincaré frame family, including its map to the ordinary Picard carrier. -/
def poincareFrameTotalFamily : (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ Type (u + 1) :=
  relativeTotalPresheaf J.toBase
    (scalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase) (poincareModulusBundle D h)).obj

/-- The same frame scheme represents the total family over the original field. -/
def poincareFrameTotalRepresentable (hd : 0 < d) :
    (poincareFrameTotalFamily D h).RepresentableBy
      ((Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :=
  relativeTotalRepresentable J.toBase _ (poincareFrameQuotientRepresentable D h hd)

/-- The total frame family satisfies actual fppf descent. -/
theorem poincareFrameTotalFamily_isSheaf (hd : 0 < d) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareFrameTotalFamily D h) := by
  have : (poincareFrameTotalFamily D h).IsRepresentable :=
    (poincareFrameTotalRepresentable D h hd).isRepresentable
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (poincareFrameTotalFamily D h)

/-- The actual parameter map classifies the ordinary underlying Poincaré family. -/
def poincareFrameTotalToPicard : poincareFrameTotalFamily D h ⟶ relSubPicPresheaf c ε P where
  app T := TypeCat.ofHom (fun x => h.representableBy.homEquiv x.1)
  naturality {T T'} g := by
    apply TypeCat.homEquiv.injective
    funext x
    exact h.representableBy.homEquiv_comp g.unop x.1

/-- The ordinary Picard projection is induced by the structure map of the same frame scheme. -/
theorem poincareFrameTotalToPicard_homEquiv (hd : 0 < d)
    {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :
    (poincareFrameTotalToPicard D h).app (op T)
        ((poincareFrameTotalRepresentable D h hd).homEquiv f) =
      h.representableBy.homEquiv
        (f ≫ (Over.homMk (poincareFrameQuotient D h hd).hom rfl)) :=
  congrArg h.representableBy.homEquiv
    (relativeTotalRepresentable_fst J.toBase _ (poincareFrameQuotientRepresentable D h hd) f)

end AlgebraicGeometry.GeneralizedJacobian
