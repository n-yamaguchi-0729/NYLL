/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.RepresentableCechTerms
import Nyll.EtaleCohomology.Sites.FilteredColimitSectionGluing
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Cech primitives in filtered colimits of injective sheaves

A cocycle on a quasi-compact geometric Cech term comes from a finite
stage. Its cocycle equation holds at a later stage, where injectivity
supplies a primitive. Naturality carries that primitive to the colimit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped Simplicial

namespace EtaleCohomology

universe u v

/-- Alternating restriction is natural in the coefficient sheaf. -/
theorem geometricCechDifferential_naturality
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{v}}
    (a : F ⟶ G) (V : C) (n : ℕ)
    (z : F.obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => V))) :
    a.hom.app (op (∏ᶜ fun _ : Fin (n + 2) => V))
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          F.obj.map ((cechNerveTerminalFrom V).δ i).op z) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        G.obj.map ((cechNerveTerminalFrom V).δ i).op
          (a.hom.app (op (∏ᶜ fun _ : Fin (n + 1) => V)) z) := by
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  erw [map_zsmul]
  congr 1
  exact ConcreteCategory.congr_hom
    (a.hom.naturality ((cechNerveTerminalFrom V).δ i).op) z

/-- Positive-degree Cech cocycles with coefficients in a filtered colimit
of injective étale sheaves have primitives whenever the two relevant
geometric powers are quasi-compact and quasi-separated. -/
theorem exists_filteredColimit_injective_geometricCech_primitive
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [∀ i, Injective (F.obj i)] (V : X.Etale) (n : ℕ)
    [QuasiCompact (terminal.from (∏ᶜ fun _ : Fin (n + 2) => V).left)]
    [QuasiSeparatedSpace (∏ᶜ fun _ : Fin (n + 2) => V).left]
    [QuasiCompact (terminal.from (∏ᶜ fun _ : Fin (n + 3) => V).left)]
    [QuasiSeparatedSpace (∏ᶜ fun _ : Fin (n + 3) => V).left]
    (z : (colimit F).obj.obj (op (∏ᶜ fun _ : Fin (n + 2) => V)))
    (hz : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      (colimit F).obj.map ((cechNerveTerminalFrom V).δ i).op z = 0) :
    ∃ b : (colimit F).obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => V)),
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (colimit F).obj.map ((cechNerveTerminalFrom V).δ i).op b = z := by
  classical
  let Γ (m : ℕ) := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (op (∏ᶜ fun _ : Fin (m + 1) => V))
  have : PreservesColimit F (Γ (n + 1)) :=
    preservesColimit_etaleSheafSections _ F
  have : PreservesColimit F (Γ (n + 2)) :=
    preservesColimit_etaleSheafSections _ F
  let c (m : ℕ) := (forget AddCommGrpCat.{u}).mapCocone
    ((Γ m).mapCocone (colimit.cocone F))
  have hc₁ : IsColimit (c (n + 1)) :=
    isColimitOfPreserves _ (isColimitOfPreserves (Γ (n + 1)) (colimit.isColimit F))
  have hc₂ : IsColimit (c (n + 2)) :=
    isColimitOfPreserves _ (isColimitOfPreserves (Γ (n + 2)) (colimit.isColimit F))
  obtain ⟨i, zi, hzi⟩ := Types.jointly_surjective_of_isColimit hc₁ z
  change (colimit.ι F i).hom.app (op (∏ᶜ fun _ : Fin (n + 2) => V)) zi = z at hzi
  let dz := ∑ k : Fin (n + 3), (-1 : ℤ) ^ (k : ℕ) •
    (F.obj i).obj.map ((cechNerveTerminalFrom V).δ k).op zi
  have hdz : (c (n + 2)).ι.app i dz = (c (n + 2)).ι.app i 0 := by
    change (colimit.ι F i).hom.app _ dz = (colimit.ι F i).hom.app _ 0
    dsimp only [dz]
    erw [geometricCechDifferential_naturality, hzi, hz, map_zero]
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hc₂ dz 0).mp hdz
  let zj := (F.map f).hom.app (op (∏ᶜ fun _ : Fin (n + 2) => V)) zi
  have hzj : ∑ k : Fin (n + 3), (-1 : ℤ) ^ (k : ℕ) •
      (F.obj j).obj.map ((cechNerveTerminalFrom V).δ k).op zj = 0 := by
    change (F.map f).hom.app _ dz = (F.map f).hom.app _ 0 at hf
    dsimp only [dz] at hf
    erw [geometricCechDifferential_naturality, map_zero] at hf
    exact hf
  obtain ⟨b, hb⟩ := exists_injective_geometricCech_primitive
    X.smallEtaleTopology V (F.obj j) n zj hzj
  refine ⟨(colimit.ι F j).hom.app _ b, ?_⟩
  erw [← geometricCechDifferential_naturality, hb]
  have hij := congrArg
    (fun a : F.obj i ⟶ colimit F =>
      a.hom.app (op (∏ᶜ fun _ : Fin (n + 2) => V)) zi)
    (colimit.w F f)
  exact hij.trans hzi

end EtaleCohomology
