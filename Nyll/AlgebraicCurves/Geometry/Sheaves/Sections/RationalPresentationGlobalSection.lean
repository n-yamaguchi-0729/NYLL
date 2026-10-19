/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleDivisorRangeEqLSpaceOn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionZeroScheme
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # A specified meromorphic value glues to an actual global line-bundle section -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- If a specified rational value belongs to every affine image of an injective
meromorphic presentation, its local preimages glue to a global section with exactly that value. -/
theorem exists_globalSection_of_affine_mem_range {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(L, U),
      φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (f : X.functionField)
    (hf : ∀ U : X.Opens, IsAffineOpen U → Nonempty U → f ∈ Set.range (φ U)) :
    ∃ s : 𝟙_ X.Modules ⟶ L,
      φ ⊤ (s.app ⊤ (toUnitSection ⊤ 1)) = f := by
  classical
  have hcharts : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hU hxU using hcharts
  have hne (x : X) : Nonempty (U x) := ⟨⟨x, hxU x⟩⟩
  choose m hm using fun x : X => hf (U x) (hU x) (hne x)
  let F : TopCat.Sheaf Ab X := ⟨L.presheaf, L.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 U m := by
    intro x y
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (U x).isOpen (U y).isOpen
      ⟨x, hxU x⟩ ⟨y, hxU y⟩
    have hxy : Nonempty (U x ⊓ U y : X.Opens) := ⟨⟨z, hz⟩⟩
    apply hinj (U x ⊓ U y) hxy
    change φ (U x ⊓ U y) (L.presheaf.map (homOfLE inf_le_left).op (m x)) =
      φ (U x ⊓ U y) (L.presheaf.map (homOfLE inf_le_right).op (m y))
    rw [hnat (U x) _ inf_le_left hxy, hnat (U y) _ inf_le_right hxy, hm x, hm y]
  have hcov : (⊤ : X.Opens) ≤ iSup U :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨s₀, hs₀, -⟩ := F.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcov m hcompat
  have hvalue : φ ⊤ s₀ = f := by
    let x := genericPoint X
    exact (hnat ⊤ (U x) le_top (hne x) s₀).symm.trans
      ((congrArg (φ (U x)) (hs₀ x)).trans (hm x))
  let fam : SheafOfModules.sections L := PresheafOfModules.sectionsMk
    (fun V => L.presheaf.map (homOfLE (le_top (a := V.unop))).op s₀)
    (by
      intro V W q
      change L.presheaf.map q (L.presheaf.map _ s₀) = _
      rw [← CategoryTheory.comp_apply, ← L.presheaf.map_comp]
      rfl)
  let s : 𝟙_ X.Modules ⟶ L := (SheafOfModules.unitHomEquiv L).symm fam
  have hs : s.app ⊤ (toUnitSection ⊤ 1) = s₀ := by
    have h := SheafOfModules.unitHomEquiv_apply_coe L s (op ⊤)
    rw [show s = (SheafOfModules.unitHomEquiv L).symm fam from rfl,
      Equiv.apply_symm_apply] at h
    change L.presheaf.map (homOfLE (le_refl (⊤ : X.Opens))).op s₀ =
      s.app ⊤ (toUnitSection ⊤ 1) at h
    have hi : L.presheaf.map (homOfLE (le_refl (⊤ : X.Opens))).op s₀ = s₀ := by
      rw [show homOfLE (le_refl (⊤ : X.Opens)) = 𝟙 ⊤ from Subsingleton.elim _ _,
        op_id, L.presheaf.map_id]
      rfl
    exact h.symm.trans hi
  exact ⟨s, (congrArg (φ ⊤) hs).trans hvalue⟩

end AlgebraicGeometry.Scheme.Modules
