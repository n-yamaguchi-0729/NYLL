/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.OverTotalMap
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! Local injectivity and surjectivity pass from a slice family to its actual total family. -/

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {S : C} (J : GrothendieckTopology C)
  {G H : (Over S)ᵒᵖ ⥤ Type (max v w)} (a : G ⟶ H)

/-- A covering family of local relative preimages also covers the same total-family section. -/
theorem overTotalMap_isLocallySurjective [Presheaf.IsLocallySurjective (J.over S) a] :
    Presheaf.IsLocallySurjective J (overTotalMap a) := by
  constructor
  rintro T ⟨t, x⟩
  have hc := (J.mem_over_iff _).mp
    (Presheaf.imageSieve_mem (J.over S) a (U := op (Over.mk t)) x)
  apply J.superset_covering ?_ hc
  intro U f hf
  obtain ⟨y, hy⟩ := (Sieve.overEquiv_iff _ f).mp hf
  refine ⟨⟨f ≫ t, y⟩, ?_⟩
  exact congrArg (fun z : H.obj (op (Over.mk (f ≫ t))) =>
    (⟨f ≫ t, z⟩ : H.OverTotal U)) hy

/-- Equality of total images reduces to equality in one actual relative fibre. -/
theorem overTotalMap_isLocallyInjective [Presheaf.IsLocallyInjective (J.over S) a] :
    Presheaf.IsLocallyInjective J (overTotalMap a) := by
  constructor
  rintro T ⟨t, x⟩ ⟨t', y⟩ h
  change (⟨t, a.app (op (Over.mk t)) x⟩ : H.OverTotal T.unop) =
    ⟨t', a.app (op (Over.mk t')) y⟩ at h
  have ht : t = t' := congrArg Sigma.fst h
  subst t'
  have hxy : a.app (op (Over.mk t)) x = a.app (op (Over.mk t)) y := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
  have hc := (J.mem_over_iff _).mp
    (Presheaf.equalizerSieve_mem (J.over S) a x y hxy)
  apply J.superset_covering ?_ hc
  intro U f hf
  have hf' := (Sieve.overEquiv_iff _ f).mp hf
  exact congrArg (fun z : G.obj (op (Over.mk (f ≫ t))) =>
    (⟨f ≫ t, z⟩ : G.OverTotal U)) hf'

end CategoryTheory.Functor
