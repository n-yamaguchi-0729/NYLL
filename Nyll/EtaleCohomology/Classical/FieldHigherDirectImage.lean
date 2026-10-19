/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.FieldHilbert90EtaleObjects
import Nyll.EtaleCohomology.Classical.HigherDirectImageResolution

/-!
# Vanishing of the first direct image of the unit sheaf from a field

For a characteristic-zero field and any morphism from its spectrum, the actual
first right derived direct image of the unit sheaf is zero. The proof uses
geometric Hilbert 90 on every base-changed étale object and the proved
sheafification computation of higher direct image.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Actual geometric Hilbert 90 annihilates the first higher direct image of
Gm along any morphism from the spectrum of a characteristic-zero field. -/
theorem etaleMultiplicativeGroup_rightDerived_pushforward_one_isZero_of_field
    (K : Type u) [Field K] [CharZero K] {Y : Scheme.{u}}
    (f : Spec (.of K) ⟶ Y) :
    IsZero (((etaleAbelianPushforward f).rightDerived 1).obj
      (etaleMultiplicativeGroupSheaf (Spec (.of K)))) := by
  let F := etaleMultiplicativeGroupSheaf (Spec (.of K))
  apply etaleRightDerivedPushforward_isZero_of_cohomologyPresheaf_eq_zero f F 1
  intro V a
  exact etaleMultiplicativeGroup_H1_eq_zero_at_etale_object_of_field K V a

end EtaleCohomology
