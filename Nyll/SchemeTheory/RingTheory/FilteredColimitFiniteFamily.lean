/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Tactic.Choose

/-!
# Finite families in an actual filtered colimit of commutative rings
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace CommRingCat

variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- A finite family in the supplied colimit lifts to a single actual diagram stage. -/
theorem lift_finite_family (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : IsColimit c) {n : ℕ} (a : Fin n → c.pt) :
    ∃ (i : I) (b : Fin n → D.obj i), ∀ k, c.ι.app i (b k) = a k := by
  classical
  have hrep (k : Fin n) : ∃ (i : I) (x : D.obj i), c.ι.app i x = a k := by
    exact Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat.{u}) hc) (a k)
  choose j x hx using hrep
  obtain ⟨i, hi⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let h (k : Fin n) : j k ⟶ i :=
    (hi (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
  refine ⟨i, fun k => D.map (h k) (x k), fun k => ?_⟩
  exact (ConcreteCategory.congr_hom (c.w (h k)) (x k)).trans (hx k)

end CommRingCat
