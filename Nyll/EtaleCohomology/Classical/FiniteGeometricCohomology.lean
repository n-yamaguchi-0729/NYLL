/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.AlgebraicallyClosedCohomology
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FinitePushforward
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Sites.FinitePushforwardStalkSurjectivity
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
public import Nyll.EtaleCohomology.Sites.SeparablyClosedFieldStalks
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Actual cohomology of finite schemes over an algebraically closed field

The product of global-section germs is an isomorphism for arbitrary module
sheaves on a finite scheme over an algebraically closed field. The existing
finite direct-image stalk formula and the identity-point germ compute this
canonical map. Finite direct image and field acyclicity also kill every
positive cohomology group, without a reducedness or étaleness assumption.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
variable {Y : Scheme.{u}} (q : Y ⟶ Spec (.of Ω))
variable (R : Type u) [CommRing R]

/-- The product of the original global-section germs over the geometric
points of a scheme with its specified structure morphism. -/
def finiteGeometricGlobalSectionsMap
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ⟶
      ∏ᶜ fun s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} =>
        ((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} R)).obj F :=
  Pi.lift (fun s => etaleGlobalSectionsGerm s.val R F)

/-- Finite direct image identifies the product of these literal germs with
the composite of the identity germ and the proved finite stalk comparison. -/
theorem finiteGeometricGlobalSectionsMap_isIso [IsFinite q]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso (finiteGeometricGlobalSectionsMap Ω q R F) := by
  let A : ModuleCat.{u} R :=
    ((etalePushforward q R).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
  let B : ModuleCat.{u} R :=
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
      (A := ModuleCat.{u} R)).obj ((etalePushforward q R).obj F)
  let S : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} → ModuleCat.{u} R :=
    fun s => ((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} R)).obj F
  let P : A ≅ F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
    etalePushforwardGlobalSectionsIso q R F
  let γ : A ⟶ B := etaleGlobalSectionsGerm (𝟙 (Spec (.of Ω))) R
    ((etalePushforward q R).obj F)
  let c : B ⟶ ∏ᶜ S := etalePushforwardStalkComparison q (𝟙 (Spec (.of Ω))) F
  have : IsIso γ := etaleGlobalSectionsGerm_identity_isIso Ω R _
  have : IsIso c := etalePushforwardStalkComparison_isIso q (𝟙 (Spec (.of Ω))) F
  have heq : P.hom ≫ finiteGeometricGlobalSectionsMap Ω q R F = γ ≫ c := by
    apply Pi.hom_ext
    intro s
    calc
      (P.hom ≫ finiteGeometricGlobalSectionsMap Ω q R F) ≫ Pi.π _ s =
          P.hom ≫ (finiteGeometricGlobalSectionsMap Ω q R F ≫ Pi.π _ s) := rfl
      _ = P.hom ≫ etaleGlobalSectionsGerm s.val R F :=
        congrArg (fun t => P.hom ≫ t) (Pi.lift_comp_π _ s)
      _ = γ ≫ etalePushforwardStalkComponent q (𝟙 (Spec (.of Ω))) s F :=
        (etalePushforwardGlobalSectionsIso_germ q R (𝟙 (Spec (.of Ω))) s F).symm
      _ = γ ≫ (c ≫ Pi.π _ s) :=
        congrArg (fun t => γ ≫ t)
          (etalePushforwardStalkComparison_π q (𝟙 (Spec (.of Ω))) s F).symm
      _ = (γ ≫ c) ≫ Pi.π _ s := rfl
  have : IsIso (P.hom ≫ finiteGeometricGlobalSectionsMap Ω q R F) :=
    heq.symm ▸ inferInstanceAs (IsIso (γ ≫ c))
  exact IsIso.of_isIso_comp_left P.hom _

private theorem modulePiIsoPi_lift_apply {ι : Type u}
    (A : ModuleCat.{u} R) (S : ι → ModuleCat.{u} R)
    (g : ∀ i : ι, A ⟶ S i) (x : A) (i : ι) :
    (ModuleCat.piIsoPi S).hom ((Pi.lift g).hom x) i = (g i).hom x := by
  have hp := congrArg
    (fun t : ∏ᶜ S ⟶ S i => t.hom ((Pi.lift g).hom x))
    (ModuleCat.piIsoPi_hom_ker_subtype S i)
  have hπ : Pi.lift g ≫ Pi.π S i = g i := Pi.lift_comp_π g i
  have hg := congrArg (fun t : A ⟶ S i => t.hom x) hπ
  exact hp.trans hg

/-- Global sections are the actual family of geometric stalks; the map is
evaluation by the original germs, rather than a chosen splitting of the scheme. -/
def finiteGeometricGlobalSectionsEquiv [IsFinite q]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ≃ₗ[R]
      (∀ s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _},
        ((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} R)).obj F) := by
  have : IsIso (finiteGeometricGlobalSectionsMap Ω q R F) :=
    finiteGeometricGlobalSectionsMap_isIso Ω q R F
  exact (asIso (finiteGeometricGlobalSectionsMap Ω q R F) ≪≫
    ModuleCat.piIsoPi (fun s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} =>
      ((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} R)).obj F)).toLinearEquiv

/-- Every coordinate of the comparison is the original global-section germ. -/
theorem finiteGeometricGlobalSectionsEquiv_apply [IsFinite q]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _}) :
    finiteGeometricGlobalSectionsEquiv Ω q R F x s = etaleGlobalSectionsGerm s.val R F x := by
  let S : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _} → ModuleCat.{u} R := fun s =>
    ((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} R)).obj F
  let A : ModuleCat.{u} R := F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))
  let g : ∀ s, A ⟶ S s := fun s => etaleGlobalSectionsGerm s.val R F
  change (ModuleCat.piIsoPi S).hom ((Pi.lift g).hom x) s = (g s).hom x
  exact modulePiIsoPi_lift_apply R A S g x s

/-- The coefficient-linear degree-zero cohomology comparison takes values
in the actual geometric stalks of the original sheaf. -/
def finiteGeometricCohomologyZeroEquiv [IsFinite q]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    etaleCohomology Y R F 0 ≃ₗ[R]
      (∀ s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = 𝟙 _},
        ((Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} R)).obj F) :=
  (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y)).trans
    (finiteGeometricGlobalSectionsEquiv Ω q R F)

/-- Every positive-degree class vanishes on a finite scheme over an
algebraically closed field, for arbitrary module coefficients. -/
theorem finiteGeometricCohomology_succ_eq_zero [IsFinite q]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : etaleCohomology Y R F (n + 1)) : x = 0 := by
  let A := Classical.forgetCoefficients.{u + 1, u, u, u}.obj F
  let e := etaleAbelianCohomologyFinitePushforwardEquiv q A (n + 1)
  have hz : e.symm x = 0 := fieldSheafCohomology_eq_zero_of_isAlgClosed Ω
    ((etaleAbelianPushforward q).obj A) n (e.symm x)
  exact e.symm.injective (hz.trans e.symm.map_zero.symm)

end EtaleCohomology
