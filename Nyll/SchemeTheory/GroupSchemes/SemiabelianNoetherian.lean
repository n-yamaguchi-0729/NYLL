/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.SemiabelianGeometry
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherianity of the actual semiabelian scheme

The source is locally of finite type over its ground field by smoothness, and
quasi-compact by descent from its torus-by-abelian extension.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsSemiabelian

variable {K : Type u} [Field K] {G : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- The actual underlying scheme of a semiabelian variety is Noetherian. -/
instance isNoetherian [IsSemiabelian G] : IsNoetherian G.X.left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian G.X.hom

end AlgebraicGeometry.IsSemiabelian
