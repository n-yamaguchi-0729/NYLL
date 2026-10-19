/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalTrace
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Integral closedness of regular domains

Regularity at the actual prime localizations supplies their integral
closedness. The local criterion then proves integral closedness of the
original domain, as needed for normalization of smooth affine charts.
-/

namespace SchemeTheory

/-- Every regular domain is integrally closed. -/
theorem isIntegrallyClosed_of_isRegularRing
    (R : Type*) [CommRing R] [IsDomain R] [IsRegularRing R] : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  exact isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime p)

end SchemeTheory
