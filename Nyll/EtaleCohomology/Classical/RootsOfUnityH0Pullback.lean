/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianPullbackLocalSections
public import Nyll.EtaleCohomology.Classical.GeometricallyConnectedH0
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Actual global sections of the Kummer kernel under pullback

The original inverse-image unit and Kummer coefficient map give the actual
map on global sections. The native H⁰ comparison identifies this map and
retains the original inclusion into units. Geometrically connected descent
therefore supplies unique lifts of the original kernel sections themselves.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : X ⟶ Y)

/-- Pullback of an actual global section of the original Kummer kernel. -/
def etaleRootsOfUnityGlobalSectionsPullback (n : ℕ) :
    (etaleRootsOfUnitySheaf Y n).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) →+
      (etaleRootsOfUnitySheaf X n).obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  (etaleAbelianPullbackLocalSectionMap q (etaleRootsOfUnitySheaf Y n) q
      ((Category.comp_id q).trans (Category.id_comp q).symm) ≫
    (etaleRootsOfUnityPullback q n).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom

/-- Native Kummer H⁰ pullback evaluates to the actual original section map. -/
theorem etaleRootsOfUnityCohomologyPullback_zero_sections (n : ℕ)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) 0) :
    let hX := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let hY := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    Sheaf.H.equiv₀ (etaleRootsOfUnitySheaf X n) hX
        (etaleRootsOfUnityCohomologyPullback q n 0 a) =
      etaleRootsOfUnityGlobalSectionsPullback q n
        (Sheaf.H.equiv₀ (etaleRootsOfUnitySheaf Y n) hY a) := by
  intro hX hY
  let l : Scheme.Etale.mk (𝟙 X) ⟶
      (etaleBaseChange q).obj (Scheme.Etale.mk (𝟙 Y)) := etaleBaseChangeLift q q
    ((Category.comp_id q).trans (Category.id_comp q).symm)
  exact (Sheaf.H.equiv₀_naturality.{u} (J := X.smallEtaleTopology)
    (F := (etaleAbelianPullback q).obj (etaleRootsOfUnitySheaf Y n))
    (G := etaleRootsOfUnitySheaf X n) hX (etaleRootsOfUnityPullback q n)
    (etaleAbelianCohomologyPullbackMap q (etaleRootsOfUnitySheaf Y n) 0 a)).symm.trans
      (congrArg
        (fun z : ((etaleAbelianPullback q).obj (etaleRootsOfUnitySheaf Y n)).obj.obj
            (op (Scheme.Etale.mk (𝟙 X))) =>
          (etaleRootsOfUnityPullback q n).hom.app (op (Scheme.Etale.mk (𝟙 X))) z)
        (etaleAbelianCohomologyPullbackMap_zero_sections q
          (etaleRootsOfUnitySheaf Y n) hY hX l a))

/-- The actual cohomological pullback retains the original inclusion of
the Kummer kernel into the sheaf of units, in every degree. -/
theorem etaleRootsOfUnityCohomologyPullback_ι (n i : ℕ)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) i) :
    Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) i
        (etaleRootsOfUnityCohomologyPullback q n i a) =
      etaleMultiplicativeGroupCohomologyPullback q i
        (Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower Y n)) i a) := by
  change Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) i
    (Sheaf.H.map (etaleRootsOfUnityPullback q n) i
      (etaleAbelianCohomologyPullbackMap q (etaleRootsOfUnitySheaf Y n) i a)) =
    Sheaf.H.map (etaleMultiplicativeGroupPullback q) i
      (etaleAbelianCohomologyPullbackMap q (etaleMultiplicativeGroupSheaf Y) i
        (Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower Y n)) i a))
  rw [← Sheaf.H.map_comp_apply, etaleRootsOfUnityPullback_ι,
    Sheaf.H.map_comp_apply, etaleAbelianCohomologyPullbackMap_naturality]

/-- Geometrically connected pullback is bijective on the actual global
sections of the original Kummer kernel, including on disconnected schemes. -/
theorem etaleRootsOfUnityGlobalSectionsPullback_bijective
    [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Y ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K)) :
    Function.Bijective (etaleRootsOfUnityGlobalSectionsPullback q n) := by
  let hX := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let hY := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y
  let eX := Sheaf.H.equiv₀.{u} (etaleRootsOfUnitySheaf X n) hX
  let eY := Sheaf.H.equiv₀.{u} (etaleRootsOfUnitySheaf Y n) hY
  have hb := etaleRootsOfUnityCohomologyPullback_zero_bijective q c hn hnK
  refine ⟨?_, ?_⟩
  · intro a b hab
    have he : etaleRootsOfUnityCohomologyPullback q n 0 (eY.symm a) =
        etaleRootsOfUnityCohomologyPullback q n 0 (eY.symm b) := by
      apply eX.injective
      rw [etaleRootsOfUnityCohomologyPullback_zero_sections,
        etaleRootsOfUnityCohomologyPullback_zero_sections,
        eY.apply_symm_apply, eY.apply_symm_apply, hab]
    exact eY.symm.injective (hb.1 he)
  · intro b
    obtain ⟨a, ha⟩ := hb.2 (eX.symm b)
    refine ⟨eY a, ?_⟩
    rw [← etaleRootsOfUnityCohomologyPullback_zero_sections, ha, eX.apply_symm_apply]

end EtaleCohomology
