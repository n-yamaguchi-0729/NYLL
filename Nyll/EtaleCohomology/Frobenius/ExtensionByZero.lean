/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ExtensionByZeroBaseChange
import Nyll.SchemeTheory.Etale.FrobeniusSquare

/-!
# Frobenius and actual extension by zero

The Frobenius square of an open immersion is cartesian. The actual
extension-by-zero base-change comparison therefore commutes extension by
zero with the existing Frobenius inverse-image functors.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] {U X : Scheme.{u}}
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] (R : Type u) [CommRing R]

/-- The actual Frobenius inverse image commutes with actual extension by
zero for any open immersion over the finite field. -/
def etaleExtensionByZeroFrobeniusIso :
    etaleExtensionByZero j R ⋙ etalePullback (X.finiteFieldFrobenius k) R ≅
      etalePullback (U.finiteFieldFrobenius k) R ⋙ etaleExtensionByZero j R :=
  etaleExtensionByZeroBaseChangeIsoOfIsPullback j (X.finiteFieldFrobenius k)
    (U.finiteFieldFrobenius k) j (Scheme.finiteFieldFrobenius_isPullback k j) R

end EtaleCohomology
