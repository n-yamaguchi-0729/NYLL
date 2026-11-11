/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Nyll.AbelianVarieties.Geometry.GroupLaw

/-!
# Affine group schemes and their Hopf algebras

Construct the coordinate Hopf algebra using the fully faithful algebraic spectrum functor.
Keep its functor of points, finite type, flatness, and commutativity comparisons explicit.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.AffineHopf

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Coordinates

open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open _root_.TensorProduct

universe v₁ v₂ u₁ u₂

section alpha

variable {R : Type u} [CommRing R]

lemma comul_unop_def (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A] :
    (Coalgebra.comul : A.unop →ₗ[R] A.unop ⊗[R] A.unop) = μ[A].unop.hom.toLinearMap := rfl

scoped instance isCocommUnop (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A] [IsCommMonObj A] :
    Coalgebra.IsCocomm R A.unop where
  comm_comp_comul := by
    have h := congr(($(IsCommMonObj.mul_comm A)).unop.hom.toLinearMap)
    simp only [unop_comp, CommAlgCat.hom_comp, AlgHom.comp_toLinearMap, unop_hom_braiding,
      CommAlgCat.braiding_hom_hom] at h
    rw [comul_unop_def]
    convert h using 2
    rfl

end alpha

section epsilon
open _root_.CategoryTheory.Functor
open _root_.CategoryTheory.Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.OplaxMonoidal]

lemma map_hom_mul {X : C} [MonObj X] [MonObj (F.obj X)]
    (hμ : F.map μ[X] = δ F X X ≫ μ[F.obj X]) {Y : C} (f g : Y ⟶ X) :
    F.map (f * g) = F.map f * F.map g := by
  simp only [Hom.mul_def, Functor.map_comp, hμ, lift_δ_assoc]

variable (hF : F.FullyFaithful) (X : C)

lemma map_mul_monObj [MonObj (F.obj X)] :
    let : MonObj X := hF.monObj X
    F.map μ[X] = δ F X X ≫ μ[F.obj X] :=
  hF.map_preimage _

omit [F.OplaxMonoidal] in
@[reassoc]
lemma map_braiding_hom_comp_δ [F.OplaxMonoidal] [BraidedCategory C] [BraidedCategory D]
    (X Y : C) :
    F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, δ_fst, δ_snd, braiding_hom_fst, ← Functor.map_comp]
  · simp only [Category.assoc, δ_fst, δ_snd, braiding_hom_snd, ← Functor.map_comp]

lemma isCommMonObj_of_fullyFaithful [BraidedCategory C] [BraidedCategory D] [MonObj (F.obj X)]
    [IsCommMonObj (F.obj X)] :
    let : MonObj X := hF.monObj X; IsCommMonObj X := by
  intro monObjX
  refine ⟨hF.map_injective ?_⟩
  simp only [Functor.map_comp, FullyFaithful.monObj_mul, FullyFaithful.map_preimage]
  rw [map_braiding_hom_comp_δ_assoc, IsCommMonObj.mul_comm]

lemma map_mul_of_fullyFaithful [MonObj (F.obj X)] {Y : C} (f g : Y ⟶ X) :
    let : MonObj X := hF.monObj X; F.map (f * g) = F.map f * F.map g := by
  intro monObjX
  exact map_hom_mul F (map_mul_monObj F hF X) f g

omit [F.OplaxMonoidal] in
lemma mul_comp_ofIso_inv {M X' Y : D} [MonObj M] (e : M ≅ X') (f₁ f₂ : Y ⟶ X') :
    let : MonObj X' := MonObj.ofIso e; (f₁ * f₂) ≫ e.inv = (f₁ ≫ e.inv) * (f₂ ≫ e.inv) := by
  intro monObjX
  exact MonObj.mul_comp f₁ f₂ e.inv

omit [F.OplaxMonoidal] in
lemma isCommMonObj_ofIso [BraidedCategory D] {M X' : D} [MonObj M] [IsCommMonObj M]
    (e : M ≅ X') : let : MonObj X' := MonObj.ofIso e; IsCommMonObj X' := by
  intro monObjX
  refine ⟨?_⟩
  rw [MonObj.ofIso_mul, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]

end epsilon

section delta

variable {R : Type u} [CommRing R] (G : Over (Spec (CommRingCat.of R)))

/-- The scalar action on global sections induced by the structure morphism. -/
@[reducible]
noncomputable scoped instance secAlgebra : Algebra R Γ(G.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop).hom.toAlgebra

lemma algebraMap_sec_def :
    algebraMap R Γ(G.left, ⊤) = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop).hom :=
  rfl

lemma ofHom_algebraMap_sec :
    CommRingCat.ofHom (algebraMap R Γ(G.left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop :=
  rfl

lemma isAffine_left [IsAffineHom G.hom] : IsAffine G.left := isAffine_of_isAffineHom G.hom

lemma isoSpec_hom_comp_specMap_algebraMap [IsAffine G.left] :
    G.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(G.left, ⊤))) = G.hom := by
  rw [ofHom_algebraMap_sec, Spec.map_comp, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The affine model is isomorphic to the spectrum of its sections over the base. -/
noncomputable def overIsoSpec [IsAffine G.left] :
    G ≅ (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R Γ(G.left, ⊤))) :=
  Over.isoMk G.left.isoSpec (isoSpec_hom_comp_specMap_algebraMap G)

@[scoped simp]
lemma overIsoSpec_hom_left [IsAffine G.left] :
    (overIsoSpec G).hom.left = G.left.toSpecΓ := rfl

@[scoped simp]
lemma overIsoSpec_inv_left [IsAffine G.left] :
    (overIsoSpec G).inv.left = G.left.isoSpec.inv := rfl

end delta

section betaA

variable (R : Type u) [CommRing R]

/-- The canonical algebraic spectrum functor from mathlib. -/
noncomputable abbrev specOver : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
  algSpec (CommRingCat.of R)

/-- Full faithfulness of the same canonical spectrum functor. -/
noncomputable abbrev specOverFullyFaithful : (specOver R).FullyFaithful :=
  algSpec.fullyFaithful

/-- Keep the canonical spectrum monoidal dictionary visible through the abbreviation. -/
noncomputable scoped instance specOverBraided : (specOver R).Braided :=
  AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of R)

@[scoped simp]
lemma specOver_map_left {A B : (CommAlgCat.{u} R)ᵒᵖ} (f : A ⟶ B) :
    ((specOver R).map f).left = Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) := rfl

end betaA

section gamma

variable {R : Type u} [CommRing R]

section
variable (G : Over (Spec (CommRingCat.of R)))

lemma secFiniteType [IsAffineHom G.hom] [LocallyOfFiniteType G.hom] : Algebra.FiniteType R Γ(G.left,
    ⊤) := by
  have : IsAffine G.left := isAffine_left G
  rw [← RingHom.finiteType_algebraMap, algebraMap_sec_def, CommRingCat.hom_comp]
  have h1 : (G.hom.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  exact h1.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
end

open WithConv in
/-- Convolution algebra maps are points of the opposite algebra group object. -/
noncomputable def convHomMulEquiv' (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A]
    (L : Type u) [CommRing L] [Algebra R L] :
    WithConv (A.unop →ₐ[R] L) ≃* (op (CommAlgCat.of R L) ⟶ A) where
  toFun φ := (show A.unop ⟶ CommAlgCat.of R L from CommAlgCat.ofHom φ.ofConv).op
  invFun f := toConv f.unop.hom
  left_inv φ := rfl
  right_inv f := rfl
  map_mul' φ ψ := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    ext c
    exact AlgHom.convMul_apply φ ψ c

@[scoped simp]
lemma convHomMulEquiv'_apply_unop_hom (A : (CommAlgCat.{u} R)ᵒᵖ) [MonObj A]
    (L : Type u) [CommRing L] [Algebra R L] (φ : WithConv (A.unop →ₐ[R] L)) :
    (convHomMulEquiv' A L φ).unop.hom = φ.ofConv := rfl

end gamma

section assembly

variable {R : Type u} [CommRing R] (G : Over (Spec (CommRingCat.of R)))

/-- The coordinate algebra, regarded as an object of the opposite algebra category. -/
noncomputable abbrev ΓOp : (CommAlgCat.{u} R)ᵒᵖ := op (CommAlgCat.of R Γ(G.left, ⊤))

lemma specOver_obj_ΓOp :
    (specOver R).obj (ΓOp G) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(G.left, ⊤)))) := rfl

variable [GrpObj G] [IsAffine G.left]

noncomputable scoped instance grpObjSpec : GrpObj ((specOver R).obj (ΓOp G)) :=
  GrpObj.ofIso (overIsoSpec G)

scoped instance isCommMonObjSpec [IsCommMonObj G] : IsCommMonObj ((specOver R).obj (ΓOp G)) :=
  isCommMonObj_ofIso (overIsoSpec G)

noncomputable scoped instance grpObjΓ : GrpObj (ΓOp G) :=
  (specOverFullyFaithful R).grpObj (ΓOp G)

/-- Reuse the monoid part of the chosen coordinate group object. -/
noncomputable scoped instance monObjΓ : MonObj (ΓOp G) :=
  (grpObjΓ G).toMonObj

scoped instance isCommMonObjΓ [IsCommMonObj G] : IsCommMonObj (ΓOp G) :=
  isCommMonObj_of_fullyFaithful (specOver R) (specOverFullyFaithful R) (ΓOp G)

/-- The canonical Hopf structure supplied by a group object in opposite algebras. -/
noncomputable abbrev hopfOfGroupObject (A : (CommAlgCat.{u} R)ᵒᵖ) [GrpObj A] :
    HopfAlgebra R A.unop := inferInstance

/-- Reuse the canonical Hopf structure on the chosen opposite algebra group object. -/
@[reducible]
noncomputable scoped instance coordinateHopf : HopfAlgebra R (ΓOp G).unop :=
  hopfOfGroupObject (ΓOp G)

variable (L : Type u) [CommRing L] [Algebra R L]

/-- Identify algebra-valued coordinate maps with points of the original affine model. -/
noncomputable def ptsEquiv :
    WithConv ((ΓOp G).unop →ₐ[R] L) ≃
      ((specOver R).obj (op (CommAlgCat.of R L)) ⟶ G) :=
  (convHomMulEquiv' (ΓOp G) L).toEquiv.trans <|
    (specOverFullyFaithful R).homEquiv.trans
      { toFun := fun f => f ≫ (overIsoSpec G).inv
        invFun := fun f => f ≫ (overIsoSpec G).hom
        left_inv := fun f => (Category.assoc _ _ _).trans <|
          (congrArg (f ≫ ·) (overIsoSpec G).inv_hom_id).trans (Category.comp_id f)
        right_inv := fun f => (Category.assoc _ _ _).trans <|
          (congrArg (f ≫ ·) (overIsoSpec G).hom_inv_id).trans (Category.comp_id f) }

lemma ptsEquiv_apply (φ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    ptsEquiv G L φ = (specOver R).map (convHomMulEquiv' (ΓOp G) L φ) ≫ (overIsoSpec G).inv :=
  rfl

lemma ptsEquiv_left (φ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    (ptsEquiv G L φ).left =
      Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ G.left.isoSpec.inv := by
  rw [ptsEquiv_apply, Over.comp_left, overIsoSpec_inv_left]
  rfl

lemma ptsEquiv_mul (φ ψ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    ptsEquiv G L (φ * ψ) = ptsEquiv G L φ * ptsEquiv G L ψ := by
  have h1 : convHomMulEquiv' (ΓOp G) L (φ * ψ) =
      convHomMulEquiv' (ΓOp G) L φ * convHomMulEquiv' (ΓOp G) L ψ := map_mul _ φ ψ
  have h2 := map_mul_of_fullyFaithful (specOver R) (specOverFullyFaithful R) (ΓOp G)
    (convHomMulEquiv' (ΓOp G) L φ) (convHomMulEquiv' (ΓOp G) L ψ)
  rw [ptsEquiv_apply, ptsEquiv_apply, ptsEquiv_apply, h1]
  exact (congrArg (· ≫ (overIsoSpec G).inv) h2).trans (mul_comp_ofIso_inv (overIsoSpec G) _ _)

lemma ptsEquiv_natural (L' : Type u) [CommRing L'] [Algebra R L'] (g : L →ₐ[R] L')
    (φ : WithConv ((ΓOp G).unop →ₐ[R] L)) :
    (ptsEquiv G L' (.toConv (g.comp φ.ofConv))).left =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (ptsEquiv G L φ).left := by
  rw [ptsEquiv_left, ptsEquiv_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end assembly

end Coordinates

open scoped Coordinates

namespace FlatUpgrade
open Coordinates
variable {R : Type u} [CommRing R] (G : Over (Spec (CommRingCat.of R)))

theorem secModuleFlat [IsAffine G.left] [Flat G.hom] : Module.Flat R Γ(G.left, ⊤) := by
  have h2 : Flat (G.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(G.left,⊤)))) := by
    rw [isoSpec_hom_comp_specMap_algebraMap G]; infer_instance
  have : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (HasRingHomProperty.Spec_iff (P := @Flat.{u})).mp
    ((MorphismProperty.cancel_left_of_respectsIso @Flat.{u} _ _).mp h2)

theorem flatΓ [GrpObj G] [IsCommMonObj G] [IsAffineHom G.hom] [Flat G.hom] :
    let : IsAffine G.left := isAffine_left G
    Module.Flat R (ΓOp G).unop := by
  intro affineG
  exact secModuleFlat G

end FlatUpgrade

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
    AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

end AbelianVarieties.NOSProofs.AffineHopf

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory AlgebraicGeometry NeronModelInfra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AbelianVarieties.NOSProofs.AffineHopf.Coordinates
open AbelianVarieties.NOSProofs.AffineHopf.FlatUpgrade
open scoped CategoryTheory.MonObj AbelianVarieties.NOSProofs.AffineHopf.Coordinates

universe u

theorem exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
    {R : Type u} [CommRing R] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    [IsAffineHom g] [Flat g] [LocallyOfFiniteType g] :
    let : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    let : IsAffine A := isAffine_of_isAffineHom g
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Algebra.FiniteType R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ (iso : H ≃ₐ[R] Γ(A, ⊤))
        (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
          (e T φ).1 =
            Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫
              A.isoSpec.inv) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (σ : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (σ.comp φ.ofConv))).1 =
            Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e T φ).1) := by
  intro sectionsAlgebra affineA
  let : IsAffine (Over.mk g).left := affineA
  classical
  obtain ⟨gE, hmul, -, -⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_eq L
  let : GrpObj (Over.mk g) := gE
  have : IsCommMonObj (Over.mk g) := by
    refine ⟨?_⟩
    have key : ∀ (a b : (Over.mk g) ⊗ (Over.mk g) ⟶ Over.mk g),
        CartesianMonoidalCategory.lift a b ≫ MonObj.mul = CartesianMonoidalCategory.lift b a ≫
          MonObj.mul := by
      intro a b
      apply (schemeHomOverEquivOverHom _ g).symm.injective
      change overHomToSchemeHomOver _ = overHomToSchemeHomOver _
      have h1 : overHomToSchemeHomOver (CartesianMonoidalCategory.lift a b ≫ MonObj.mul) =
          L.mul _ (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := hmul _ a b
      have h2 : overHomToSchemeHomOver (CartesianMonoidalCategory.lift b a ≫ MonObj.mul) =
          L.mul _ (overHomToSchemeHomOver b) (overHomToSchemeHomOver a) := hmul _ b a
      exact h1.trans ((hcomm _ _ _).trans h2.symm)
    have h := key (CartesianMonoidalCategory.snd _ _) (CartesianMonoidalCategory.fst _ _)
    rw [CartesianMonoidalCategory.lift_snd_fst, CartesianMonoidalCategory.lift_fst_snd,
      Category.id_comp] at h
    exact h
  have : IsAffineHom (Over.mk g).hom := by change IsAffineHom g; infer_instance
  have : Flat (Over.mk g).hom := by change Flat g; infer_instance
  have : LocallyOfFiniteType (Over.mk g).hom := by change LocallyOfFiniteType g; infer_instance
  let iso : (ΓOp (Over.mk g)).unop ≃ₐ[R] Γ(A, ⊤) := { (RingEquiv.refl _) with commutes' := fun r =>
    rfl }
  refine ⟨(ΓOp (Over.mk g)).unop, inferInstance, coordinateHopf (Over.mk g), secFiniteType (Over.mk
    g),
    flatΓ (Over.mk g), isCocommUnop (ΓOp (Over.mk g)), iso,
    fun T _ _ => (ptsEquiv (Over.mk g) T).trans (schemeHomOverEquivOverHom _ g).symm, ?_, ?_, ?_⟩
  · intro T _ _ φ
    change (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) φ)).1 = _
    rw [overHomToSchemeHomOver_coe, ptsEquiv_left]
    rfl
  · intro T _ _ φ ψ
    change overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) (φ * ψ)) =
      L.mul _ (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T) φ)) (overHomToSchemeHomOver
        ((ptsEquiv (Over.mk g) T) ψ))
    rw [ptsEquiv_mul (Over.mk g) T φ ψ, ← hmul]
    congr 1
  · intro T T' _ _ _ _ σ φ
    change (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T') (.toConv (σ.comp φ.ofConv)))).1 =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (overHomToSchemeHomOver ((ptsEquiv (Over.mk g) T)
        φ)).1
    rw [overHomToSchemeHomOver_coe, overHomToSchemeHomOver_coe]
    exact ptsEquiv_natural (Over.mk g) T T' σ φ

end GoodReductionJacobian.RelativeGroupLaw
end
