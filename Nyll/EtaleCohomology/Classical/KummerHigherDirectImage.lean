/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.RightDerivedOneSheafification
import Nyll.EtaleCohomology.Classical.KummerPresheafCokernel
import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward

/-!
# Actual Kummer first higher direct image from a field

The natural Kummer presheaf presentation and the canonical
injective-presentation comparison identify actual first higher direct
image with the cokernel of the actual direct-image power map.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The actual first higher direct image of roots of unity from a
characteristic-zero field is the actual direct-image power cokernel. -/
def etaleKummerRightDerivedOneCokernelIso_of_field
    (K : Type u) [Field K] [CharZero K] {Y : Scheme.{u}}
    (f : Spec (.of K) ⟶ Y) {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    ((etaleAbelianPushforward f).rightDerived 1).obj
      (etaleRootsOfUnitySheaf (Spec (.of K)) n) ≅
        cokernel ((etaleAbelianPushforward f).map
          (etaleMultiplicativeGroupPower (Spec (.of K)) n)) := by
  let X := Spec (.of K)
  let G := etaleAbelianPushforward f
  let W := (Functor.whiskeringLeft Y.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u}).obj
    (etaleBaseChange f).op
  let A := presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  let H := W ⋙ A
  have : H.Additive := by dsimp [H, W, A]; infer_instance
  have : PreservesFiniteColimits H := by dsimp [H, W, A]; infer_instance
  let M := etaleMultiplicativeGroupSheaf X
  let p := etaleMultiplicativeGroupPower X n
  let e := asIso ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).counit.app
    (G.obj M))
  have he : H.map p.hom ≫ e.hom = e.hom ≫ G.map p := by
    have he := (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).counit.naturality
      (G.map p)
    change _ = _ at he
    exact he
  exact etaleRightDerivedOneSheafificationIso f (etaleRootsOfUnitySheaf X n) ≪≫
    H.mapIso (etaleKummerPresheafCokernelIso_of_field K hn hnK).symm ≪≫
      PreservesCokernel.iso H p.hom ≪≫
        cokernel.mapIso (f := H.map p.hom) (G.map p) e e he

/-- The actual first higher direct image is the quotient by multiplication by n of
the generic-unit cokernel whenever n is invertible on the target. -/
def etaleKummerRightDerivedOneUnitQuotientIso_of_field
    (K : Type u) [Field K] [CharZero K] {Y : Scheme.{u}}
    (f : Spec (.of K) ⟶ Y) {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : Γ(Spec (.of K), ⊤)))
    (hnY : IsUnit (n : Γ(Y, ⊤))) :
    ((etaleAbelianPushforward f).rightDerived 1).obj
      (etaleRootsOfUnitySheaf (Spec (.of K)) n) ≅
      cokernel (n • 𝟙 (cokernel (etaleMultiplicativeGroupToPushforward f))) :=
  etaleKummerRightDerivedOneCokernelIso_of_field K f hn hnK ≪≫
    etalePushforwardPowerCokernelIso f hn hnY

end EtaleCohomology
