/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Pullback comparisons and separated gluing

Separatedness from an open cover and the canonical comparison between iterated pullbacks.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_Schemes_IsSeparatedOfIsOpenImmersionOfIsPullbackOfIsClosedImmersionLift


universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SepGlue21

variable {S Y' : Scheme.{u}} (f' : Y' ⟶ S)

/-- The pullback comparison induced by the structural morphism to the base. -/
noncomputable abbrev δ {P Q : Scheme.{u}} (jP : P ⟶ Y') (jQ : Q ⟶ Y') :
    pullback jP jQ ⟶ pullback (jP ≫ f') (jQ ≫ f') :=
  pullback.map jP jQ (jP ≫ f') (jQ ≫ f') (𝟙 P) (𝟙 Q) f'
    (Category.id_comp _).symm (Category.id_comp _).symm

theorem isClosedImmersion_δ_self {P : Scheme.{u}} (j : P ⟶ Y') [Mono j]
    [IsClosedImmersion (pullback.diagonal (j ≫ f'))] : IsClosedImmersion (δ f' j j) := by
  have : IsIso (pullback.diagonal j) := inferInstance
  have h : δ f' j j = inv (pullback.diagonal j) ≫ pullback.diagonal (j ≫ f') := by
    rw [IsIso.eq_inv_comp]
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id]
    · simp only [δ, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id]
  rw [h]; infer_instance

theorem isClosedImmersion_δ_of_isPullback {A B U : Scheme.{u}} (jA : A ⟶ Y') (jB : B ⟶ Y')
    (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
    (hΓ : IsClosedImmersion (pullback.lift uA uB
      (by rw [← Category.assoc, hsq.w, Category.assoc]) : U ⟶ pullback (jA ≫ f') (jB ≫ f'))) :
    IsClosedImmersion (δ f' jA jB) := by
  have h1 : hsq.isoPullback.hom ≫ δ f' jA jB =
      pullback.lift uA uB (by rw [← Category.assoc, hsq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, Category.comp_id,
        IsPullback.isoPullback_hom_fst]
    · simp only [δ, Category.assoc, pullback.lift_snd, Category.comp_id,
        IsPullback.isoPullback_hom_snd]
  have h2 : δ f' jA jB = hsq.isoPullback.inv ≫
      pullback.lift uA uB (by rw [← Category.assoc, hsq.w, Category.assoc]) := by
    rw [← h1, Iso.inv_hom_id_assoc]
  rw [h2]; infer_instance

theorem isClosedImmersion_δ_symm {A B : Scheme.{u}} (jA : A ⟶ Y') (jB : B ⟶ Y')
    [IsClosedImmersion (δ f' jA jB)] : IsClosedImmersion (δ f' jB jA) := by
  have h : δ f' jB jA = (pullbackSymmetry jB jA).hom ≫ δ f' jA jB ≫
      (pullbackSymmetry (jA ≫ f') (jB ≫ f')).hom := by
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  rw [h]; infer_instance

end SepGlue21

open SepGlue21 in
theorem
  _root_.AlgebraicGeometry.isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
    {S Y' A B U : Scheme.{u}} (f' : Y' ⟶ S)
    (jA : A ⟶ Y') (jB : B ⟶ Y') [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hcov : Set.range jA.base ∪ Set.range jB.base = Set.univ)
    (fA : A ⟶ S) (fB : B ⟶ S) (hA : jA ≫ f' = fA) (hB : jB ≫ f' = fB)
    [IsSeparated fA] [IsSeparated fB]
    (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
    (hΓ : IsClosedImmersion
      (pullback.lift uA uB (by rw [← hA, ← hB, ← Category.assoc, hsq.w, Category.assoc]) :
        U ⟶ pullback fA fB)) :
    IsSeparated f' := by
  classical
  subst hA hB
  let XU : Bool → Scheme.{u} := fun b => cond b A B
  let fU : ∀ b : Bool, XU b ⟶ Y' := fun b => match b with
    | true => jA
    | false => jB
  have hfU : ∀ b : Bool, IsOpenImmersion (fU b) := by
    intro b; cases b
    · change IsOpenImmersion jB; infer_instance
    · change IsOpenImmersion jA; infer_instance
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Bool XU fU (by
    intro y
    have hy : y ∈ Set.range jA.base ∪ Set.range jB.base := by rw [hcov]; trivial
    rcases hy with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨true, x, hx⟩
    · exact ⟨false, x, hx⟩) hfU
  have hδ : ∀ a b : Bool, IsClosedImmersion (δ f' (𝒰.f a) (𝒰.f b)) := by
    intro a b
    cases a <;> cases b
    · change IsClosedImmersion (δ f' jB jB); exact isClosedImmersion_δ_self f' jB
    · change IsClosedImmersion (δ f' jB jA)
      have : IsClosedImmersion (δ f' jA jB) :=
        isClosedImmersion_δ_of_isPullback f' jA jB uA uB hsq hΓ
      exact isClosedImmersion_δ_symm f' jA jB
    · change IsClosedImmersion (δ f' jA jB)
      exact isClosedImmersion_δ_of_isPullback f' jA jB uA uB hsq hΓ
    · change IsClosedImmersion (δ f' jA jA); exact isClosedImmersion_δ_self f' jA
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f' f')
  rintro ⟨a, b⟩
  have hP := pullback_map_diagonal_isPullback (𝒰.f a) (𝒰.f b) f'
  have e : hP.isoPullback.hom ≫ pullback.snd _ _ = δ f' (𝒰.f a) (𝒰.f b) := hP.isoPullback_hom_snd
  have h3 : IsClosedImmersion (hP.isoPullback.hom ≫ pullback.snd _ _) := by rw [e]; exact hδ a b
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hP.isoPullback.hom _).mp h3

end Reduction_Support_Schemes_IsSeparatedOfIsOpenImmersionOfIsPullbackOfIsClosedImmersionLift
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_Schemes_IsIsoLiftBaseChangeFstBaseChangeSnd

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd
    {S S' Z X : Scheme.{u}} (z : Z ⟶ S) (f : X ⟶ S) (ι : S' ⟶ S) :
    IsIso
      (pullback.lift
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.fst z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.snd z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by
            rw [Category.assoc, ← pullback.condition (f := z) (g := f)]
            exact pullback.condition))
        (by rw [pullback.lift_snd, pullback.lift_snd]) :
        pullback (pullback.fst z f ≫ z) ι ⟶ pullback (pullback.snd z ι) (pullback.snd f ι)) := by
  have wA : (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst z ι) ≫ z =
      (pullback.snd (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst f ι) ≫ f := by
    have h1 : pullback.fst z ι ≫ z = pullback.snd z ι ≫ ι := pullback.condition
    have h2 : pullback.fst f ι ≫ f = pullback.snd f ι ≫ ι := pullback.condition
    have h3 : pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd z ι =
        pullback.snd (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd f ι := pullback.condition
    simp only [Category.assoc, h1, h2]
    rw [← Category.assoc, h3, Category.assoc]
  let A : pullback (pullback.snd z ι) (pullback.snd f ι) ⟶ pullback z f :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst z ι) (pullback.snd _ _ ≫ pullback.fst f ι) wA
  have hA1 : A ≫ pullback.fst z f = pullback.fst _ _ ≫ pullback.fst z ι := pullback.lift_fst _ _ _
  have hA2 : A ≫ pullback.snd z f = pullback.snd _ _ ≫ pullback.fst f ι := pullback.lift_snd _ _ _
  have wAB : A ≫ (pullback.fst z f ≫ z) =
      (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd z ι) ≫ ι := by
    rw [← Category.assoc, hA1, Category.assoc, Category.assoc]
    exact congrArg (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ ·) pullback.condition
  let inv : pullback (pullback.snd z ι) (pullback.snd f ι) ⟶ pullback (pullback.fst z f ≫ z) ι :=
    pullback.lift A (pullback.fst _ _ ≫ pullback.snd z ι) wAB
  have hI1 : inv ≫ pullback.fst (pullback.fst z f ≫ z) ι = A := pullback.lift_fst _ _ _
  have hI2 : inv ≫ pullback.snd (pullback.fst z f ≫ z) ι =
      pullback.fst _ _ ≫ pullback.snd z ι := pullback.lift_snd _ _ _
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, reassoc_of% hI1, hA1,
          pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [Category.assoc, Category.id_comp, reassoc_of% hI1, hA2,
          pullback.lift_snd_assoc, pullback.lift_fst]
    · simp only [Category.assoc, Category.id_comp, hI2,
        pullback.lift_fst_assoc, pullback.lift_snd]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst,
          reassoc_of% hI1, hA1]
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst_assoc,
          pullback.lift_snd, hI2]
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_snd_assoc, pullback.lift_fst,
          reassoc_of% hI1, hA2]
      · simp only [Category.assoc, Category.id_comp, pullback.lift_snd, hI2]
        exact pullback.condition

end Reduction_Support_Schemes_IsIsoLiftBaseChangeFstBaseChangeSnd
end NOSProofs
end AbelianVarieties
end
